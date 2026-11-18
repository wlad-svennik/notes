import Mathlib.Tactic
import Mathlib.Data.Nat.Pairing
import Lean

/-!
# Hosts: structures with Separation and Collection for every first-order formula

A *host* is a structure `(W, ∈, <*)` in which the overlapping construction of a model of tangled
type theory can be carried out. The height of the model is a number of the host, so the result
applies at heights that are not standard numbers.

This file contains the formulas, satisfaction, the axioms of a host, the reduction of formulas
with additional definable relation symbols to pure formulas, and a tactic `hdef` that turns a
Lean statement about elements of the host into a formula, so that Separation and Collection can
be applied to predicates written in Lean.
-/

set_option autoImplicit false

/-- First-order formulas in the language `{∈, <*, =}` with named variables, and with additional
ternary relation symbols `rel k`. A formula is *pure* if it has no additional symbols. -/
inductive Form : Type
  | mem (x y : ℕ)
  | lt (x y : ℕ)
  | eq (x y : ℕ)
  | rel (k x y z : ℕ)
  | tru
  | fls
  | neg (φ : Form)
  | and (φ ψ : Form)
  | or (φ ψ : Form)
  | imp (φ ψ : Form)
  | iff (φ ψ : Form)
  | all (x : ℕ) (φ : Form)
  | ex (x : ℕ) (φ : Form)

/-- Change the value of one variable. -/
def upd {W : Type} (ρ : ℕ → W) (x : ℕ) (a : W) : ℕ → W :=
  fun n => cond (Nat.beq n x) a (ρ n)

theorem upd_same {W : Type} (ρ : ℕ → W) (x : ℕ) (a : W) : upd ρ x a x = a := by
  simp [upd]

theorem upd_ne {W : Type} (ρ : ℕ → W) {x n : ℕ} (a : W) (h : n ≠ x) : upd ρ x a n = ρ n := by
  have : Nat.beq n x = false := by
    cases hb : Nat.beq n x
    · rfl
    · exact (h (Nat.eq_of_beq_eq_true hb)).elim
  simp [upd, this]

/-- The assignment given by a list of values, with a default value. -/
def env {W : Type} (d : W) : List W → ℕ → W
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, n + 1 => env d l n

/-- The value of a list of ternary relations at an index, `False` outside the list. -/
def relAt {W : Type} : List (W → W → W → Prop) → ℕ → W → W → W → Prop
  | [], _ => fun _ _ _ => False
  | R :: _, 0 => R
  | _ :: l, n + 1 => relAt l n

/-- Satisfaction, with an interpretation `I` of the additional relation symbols. -/
def Holds {W : Type} (mem lt : W → W → Prop) (I : ℕ → W → W → W → Prop) :
    Form → (ℕ → W) → Prop
  | .mem x y, ρ => mem (ρ x) (ρ y)
  | .lt x y, ρ => lt (ρ x) (ρ y)
  | .eq x y, ρ => ρ x = ρ y
  | .rel k x y z, ρ => I k (ρ x) (ρ y) (ρ z)
  | .tru, _ => True
  | .fls, _ => False
  | .neg φ, ρ => ¬ Holds mem lt I φ ρ
  | .and φ ψ, ρ => Holds mem lt I φ ρ ∧ Holds mem lt I ψ ρ
  | .or φ ψ, ρ => Holds mem lt I φ ρ ∨ Holds mem lt I ψ ρ
  | .imp φ ψ, ρ => Holds mem lt I φ ρ → Holds mem lt I ψ ρ
  | .iff φ ψ, ρ => (Holds mem lt I φ ρ ↔ Holds mem lt I ψ ρ)
  | .all x φ, ρ => ∀ a, Holds mem lt I φ (upd ρ x a)
  | .ex x φ, ρ => ∃ a, Holds mem lt I φ (upd ρ x a)

/-- A formula without additional relation symbols. -/
def Form.Pure : Form → Prop
  | .mem _ _ => True
  | .lt _ _ => True
  | .eq _ _ => True
  | .rel _ _ _ _ => False
  | .tru => True
  | .fls => True
  | .neg φ => φ.Pure
  | .and φ ψ => φ.Pure ∧ ψ.Pure
  | .or φ ψ => φ.Pure ∧ ψ.Pure
  | .imp φ ψ => φ.Pure ∧ ψ.Pure
  | .iff φ ψ => φ.Pure ∧ ψ.Pure
  | .all _ φ => φ.Pure
  | .ex _ φ => φ.Pure

/-- Rename the variables. -/
def Form.map (f : ℕ → ℕ) : Form → Form
  | .mem x y => .mem (f x) (f y)
  | .lt x y => .lt (f x) (f y)
  | .eq x y => .eq (f x) (f y)
  | .rel k x y z => .rel k (f x) (f y) (f z)
  | .tru => .tru
  | .fls => .fls
  | .neg φ => .neg (φ.map f)
  | .and φ ψ => .and (φ.map f) (ψ.map f)
  | .or φ ψ => .or (φ.map f) (ψ.map f)
  | .imp φ ψ => .imp (φ.map f) (ψ.map f)
  | .iff φ ψ => .iff (φ.map f) (ψ.map f)
  | .all x φ => .all (f x) (φ.map f)
  | .ex x φ => .ex (f x) (φ.map f)

theorem Form.pure_map (f : ℕ → ℕ) : ∀ φ : Form, φ.Pure → (φ.map f).Pure
  | .mem _ _, _ => trivial
  | .lt _ _, _ => trivial
  | .eq _ _, _ => trivial
  | .rel _ _ _ _, h => h
  | .tru, _ => trivial
  | .fls, _ => trivial
  | .neg φ, h => Form.pure_map f φ h
  | .and φ ψ, h => ⟨Form.pure_map f φ h.1, Form.pure_map f ψ h.2⟩
  | .or φ ψ, h => ⟨Form.pure_map f φ h.1, Form.pure_map f ψ h.2⟩
  | .imp φ ψ, h => ⟨Form.pure_map f φ h.1, Form.pure_map f ψ h.2⟩
  | .iff φ ψ, h => ⟨Form.pure_map f φ h.1, Form.pure_map f ψ h.2⟩
  | .all _ φ, h => Form.pure_map f φ h
  | .ex _ φ, h => Form.pure_map f φ h

theorem upd_comp {W : Type} (ρ : ℕ → W) {f : ℕ → ℕ} (hf : Function.Injective f) (x : ℕ) (a : W) :
    (upd ρ (f x) a) ∘ f = upd (ρ ∘ f) x a := by
  funext n
  by_cases h : n = x
  · subst h
    simp [upd_same]
  · have h' : f n ≠ f x := fun e => h (hf e)
    simp [upd_ne _ _ h, upd_ne _ _ h']

/-- Renaming the variables by an injective map. -/
theorem holds_map {W : Type} (mem lt : W → W → Prop) (I : ℕ → W → W → W → Prop) {f : ℕ → ℕ}
    (hf : Function.Injective f) :
    ∀ (φ : Form) (ρ : ℕ → W), Holds mem lt I (φ.map f) ρ ↔ Holds mem lt I φ (ρ ∘ f)
  | .mem _ _, _ => Iff.rfl
  | .lt _ _, _ => Iff.rfl
  | .eq _ _, _ => Iff.rfl
  | .rel _ _ _ _, _ => Iff.rfl
  | .tru, _ => Iff.rfl
  | .fls, _ => Iff.rfl
  | .neg φ, ρ => not_congr (holds_map mem lt I hf φ ρ)
  | .and φ ψ, ρ => and_congr (holds_map mem lt I hf φ ρ) (holds_map mem lt I hf ψ ρ)
  | .or φ ψ, ρ => or_congr (holds_map mem lt I hf φ ρ) (holds_map mem lt I hf ψ ρ)
  | .imp φ ψ, ρ => imp_congr (holds_map mem lt I hf φ ρ) (holds_map mem lt I hf ψ ρ)
  | .iff φ ψ, ρ => iff_congr (holds_map mem lt I hf φ ρ) (holds_map mem lt I hf ψ ρ)
  | .all x φ, ρ => forall_congr' fun a => by
      rw [holds_map mem lt I hf φ (upd ρ (f x) a), upd_comp ρ hf]
  | .ex x φ, ρ => exists_congr fun a => by
      rw [holds_map mem lt I hf φ (upd ρ (f x) a), upd_comp ρ hf]

/-- A pure formula does not depend on the interpretation of the additional symbols. -/
theorem holds_pure {W : Type} (mem lt : W → W → Prop) (I J : ℕ → W → W → W → Prop) :
    ∀ (φ : Form), φ.Pure → ∀ ρ : ℕ → W, Holds mem lt I φ ρ ↔ Holds mem lt J φ ρ
  | .mem _ _, _, _ => Iff.rfl
  | .lt _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .rel _ _ _ _, h, _ => h.elim
  | .tru, _, _ => Iff.rfl
  | .fls, _, _ => Iff.rfl
  | .neg φ, h, ρ => not_congr (holds_pure mem lt I J φ h ρ)
  | .and φ ψ, h, ρ => and_congr (holds_pure mem lt I J φ h.1 ρ) (holds_pure mem lt I J ψ h.2 ρ)
  | .or φ ψ, h, ρ => or_congr (holds_pure mem lt I J φ h.1 ρ) (holds_pure mem lt I J ψ h.2 ρ)
  | .imp φ ψ, h, ρ => imp_congr (holds_pure mem lt I J φ h.1 ρ) (holds_pure mem lt I J ψ h.2 ρ)
  | .iff φ ψ, h, ρ => iff_congr (holds_pure mem lt I J φ h.1 ρ) (holds_pure mem lt I J ψ h.2 ρ)
  | .all _ φ, h, _ => forall_congr' fun _ => holds_pure mem lt I J φ h _
  | .ex _ φ, h, _ => exists_congr fun _ => holds_pure mem lt I J φ h _

/-- The interpretation in which no additional relation holds. -/
def noRel {W : Type} : ℕ → W → W → W → Prop := fun _ _ _ _ => False

/-- A host. Separation, Collection and the least-element principle are assumed for pure
formulas. -/
structure Host where
  W : Type
  mem : W → W → Prop
  lt : W → W → Prop
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  pair : ∀ x y, ∃ p, ∀ z, mem z p ↔ z = x ∨ z = y
  union : ∀ x, ∃ u, ∀ z, mem z u ↔ ∃ y, mem y x ∧ mem z y
  inf : ∃ w, (∃ e, mem e w ∧ ∀ z, ¬ mem z e) ∧
    ∀ x, mem x w → ∃ s, mem s w ∧ ∀ z, mem z s ↔ mem z x ∨ z = x
  sep : ∀ (φ : Form), φ.Pure → ∀ (ρ : ℕ → W) (x : ℕ) (a : W),
    ∃ b, ∀ y, mem y b ↔ mem y a ∧ Holds mem lt noRel φ (upd ρ x y)
  coll : ∀ (φ : Form), φ.Pure → ∀ (ρ : ℕ → W) (x y : ℕ) (a : W),
    (∀ u, mem u a → ∃ v, Holds mem lt noRel φ (upd (upd ρ x u) y v)) →
    ∃ b, ∀ u, mem u a → ∃ v, mem v b ∧ Holds mem lt noRel φ (upd (upd ρ x u) y v)
  lt_irrefl : ∀ x, ¬ lt x x
  lt_trans : ∀ x y z, lt x y → lt y z → lt x z
  lt_tri : ∀ x y, lt x y ∨ x = y ∨ lt y x
  lt_least : ∀ (φ : Form), φ.Pure → ∀ (ρ : ℕ → W) (x : ℕ) (a : W),
    Holds mem lt noRel φ (upd ρ x a) →
    ∃ m, Holds mem lt noRel φ (upd ρ x m) ∧ ∀ b, lt b m → ¬ Holds mem lt noRel φ (upd ρ x b)
  mem_lt : ∀ x y, mem x y → lt x y

theorem Host.nonempty (H : Host) : Nonempty H.W :=
  let ⟨w, _⟩ := H.inf
  ⟨w⟩

/-- A default element. -/
noncomputable def Host.dflt (H : Host) : H.W := Classical.choice H.nonempty

instance Host.instMem (H : Host) : Membership H.W H.W := ⟨fun s x => H.mem x s⟩

/-- `P` is given by a pure formula with parameters. -/
def Def1 (H : Host) (P : H.W → Prop) : Prop :=
  ∃ (φ : Form) (ρ : ℕ → H.W) (x : ℕ), φ.Pure ∧
    ∀ a, P a ↔ Holds H.mem H.lt noRel φ (upd ρ x a)

/-- `R` is given by a pure formula with parameters. -/
def Def2 (H : Host) (R : H.W → H.W → Prop) : Prop :=
  ∃ (φ : Form) (ρ : ℕ → H.W) (x y : ℕ), φ.Pure ∧ x ≠ y ∧
    ∀ a b, R a b ↔ Holds H.mem H.lt noRel φ (upd (upd ρ x a) y b)

/-- `R` is given by a pure formula with parameters. -/
def Def3 (H : Host) (R : H.W → H.W → H.W → Prop) : Prop :=
  ∃ (φ : Form) (ρ : ℕ → H.W) (x y z : ℕ), φ.Pure ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ∀ a b c, R a b c ↔ Holds H.mem H.lt noRel φ (upd (upd (upd ρ x a) y b) z c)

/-! ## Additional relation symbols that are definable can be eliminated -/

section elim

variable (H : Host)

/-- A list of ternary relations all of which are definable. -/
def AllDef3 : List (H.W → H.W → H.W → Prop) → Prop
  | [] => True
  | R :: l => Def3 H R ∧ AllDef3 l

theorem def3_false : Def3 H (fun _ _ _ => False) :=
  ⟨.fls, fun _ => H.dflt, 0, 1, 2, trivial, by decide, by decide, by decide, fun _ _ _ => Iff.rfl⟩

theorem def3_relAt : ∀ (l : List (H.W → H.W → H.W → Prop)), AllDef3 H l →
    ∀ k, Def3 H (relAt l k)
  | [], _, _ => def3_false H
  | _ :: _, h, 0 => h.1
  | _ :: l, h, k + 1 => def3_relAt l h.2 k

variable {H}

/-- The data chosen for each additional symbol. -/
structure RelData (I : ℕ → H.W → H.W → H.W → Prop) where
  φ : ℕ → Form
  ρ : ℕ → ℕ → H.W
  x : ℕ → ℕ
  y : ℕ → ℕ
  z : ℕ → ℕ
  pure : ∀ k, (φ k).Pure
  xy : ∀ k, x k ≠ y k
  xz : ∀ k, x k ≠ z k
  yz : ∀ k, y k ≠ z k
  spec : ∀ k a b c, I k a b c ↔
    Holds H.mem H.lt noRel (φ k) (upd (upd (upd (ρ k) (x k) a) (y k) b) (z k) c)

theorem exists_relData {I : ℕ → H.W → H.W → H.W → Prop} (hI : ∀ k, Def3 H (I k)) :
    Nonempty (RelData I) := by
  choose φ ρ x y z h1 h2 h3 h4 h5 using hI
  exact ⟨⟨φ, ρ, x, y, z, h1, h2, h3, h4, h5⟩⟩

/-- Eliminate the additional symbols. Our variables are renamed `n ↦ pair 0 n`, the variables of
the definition of the symbol `k` are renamed `n ↦ pair (k + 1) n`. -/
def elimF {I : ℕ → H.W → H.W → H.W → Prop} (D : RelData I) : Form → Form
  | .mem x y => .mem (Nat.pair 0 x) (Nat.pair 0 y)
  | .lt x y => .lt (Nat.pair 0 x) (Nat.pair 0 y)
  | .eq x y => .eq (Nat.pair 0 x) (Nat.pair 0 y)
  | .rel k x y z =>
    .ex (Nat.pair (k + 1) (D.x k)) (.ex (Nat.pair (k + 1) (D.y k)) (.ex (Nat.pair (k + 1) (D.z k))
      (.and (.eq (Nat.pair (k + 1) (D.x k)) (Nat.pair 0 x))
        (.and (.eq (Nat.pair (k + 1) (D.y k)) (Nat.pair 0 y))
          (.and (.eq (Nat.pair (k + 1) (D.z k)) (Nat.pair 0 z))
            ((D.φ k).map (Nat.pair (k + 1))))))))
  | .tru => .tru
  | .fls => .fls
  | .neg φ => .neg (elimF D φ)
  | .and φ ψ => .and (elimF D φ) (elimF D ψ)
  | .or φ ψ => .or (elimF D φ) (elimF D ψ)
  | .imp φ ψ => .imp (elimF D φ) (elimF D ψ)
  | .iff φ ψ => .iff (elimF D φ) (elimF D ψ)
  | .all x φ => .all (Nat.pair 0 x) (elimF D φ)
  | .ex x φ => .ex (Nat.pair 0 x) (elimF D φ)

theorem pure_elimF {I : ℕ → H.W → H.W → H.W → Prop} (D : RelData I) : ∀ φ : Form, (elimF D φ).Pure
  | .mem _ _ => trivial
  | .lt _ _ => trivial
  | .eq _ _ => trivial
  | .rel k _ _ _ => ⟨trivial, trivial, trivial, Form.pure_map _ _ (D.pure k)⟩
  | .tru => trivial
  | .fls => trivial
  | .neg φ => pure_elimF D φ
  | .and φ ψ => ⟨pure_elimF D φ, pure_elimF D ψ⟩
  | .or φ ψ => ⟨pure_elimF D φ, pure_elimF D ψ⟩
  | .imp φ ψ => ⟨pure_elimF D φ, pure_elimF D ψ⟩
  | .iff φ ψ => ⟨pure_elimF D φ, pure_elimF D ψ⟩
  | .all _ φ => pure_elimF D φ
  | .ex _ φ => pure_elimF D φ

/-- The merged assignment. -/
def merge {I : ℕ → H.W → H.W → H.W → Prop} (D : RelData I) (ρ : ℕ → H.W) : ℕ → H.W :=
  fun m => match (Nat.unpair m).1 with
    | 0 => ρ (Nat.unpair m).2
    | k + 1 => D.ρ k (Nat.unpair m).2

theorem merge_zero {I : ℕ → H.W → H.W → H.W → Prop} (D : RelData I) (ρ : ℕ → H.W) (n : ℕ) :
    merge D ρ (Nat.pair 0 n) = ρ n := by
  simp [merge, Nat.unpair_pair]

theorem merge_succ {I : ℕ → H.W → H.W → H.W → Prop} (D : RelData I) (ρ : ℕ → H.W) (k n : ℕ) :
    merge D ρ (Nat.pair (k + 1) n) = D.ρ k n := by
  simp [merge, Nat.unpair_pair]

theorem pair_inj_right (c : ℕ) : Function.Injective (Nat.pair c) := fun a b h => by
  have := congrArg Nat.unpair h
  simp [Nat.unpair_pair] at this
  exact this

theorem pair_ne_of_fst {c c' n n' : ℕ} (h : c ≠ c') : Nat.pair c n ≠ Nat.pair c' n' := fun e => by
  have := congrArg Nat.unpair e
  simp [Nat.unpair_pair] at this
  exact h this.1

theorem merge_upd {I : ℕ → H.W → H.W → H.W → Prop} (D : RelData I) (ρ : ℕ → H.W) (x : ℕ)
    (a : H.W) : upd (merge D ρ) (Nat.pair 0 x) a = merge D (upd ρ x a) := by
  funext m
  by_cases h : m = Nat.pair 0 x
  · subst h
    rw [upd_same, merge_zero, upd_same]
  · rw [upd_ne _ _ h]
    obtain ⟨c, n, rfl⟩ : ∃ c n, m = Nat.pair c n := ⟨_, _, (Nat.pair_unpair m).symm⟩
    cases c with
    | zero =>
      rw [merge_zero, merge_zero]
      have hn : n ≠ x := fun e => h (by rw [e])
      rw [upd_ne _ _ hn]
    | succ k => rw [merge_succ, merge_succ]

theorem holds_elimF {I : ℕ → H.W → H.W → H.W → Prop} (D : RelData I) :
    ∀ (φ : Form) (ρ : ℕ → H.W),
      Holds H.mem H.lt noRel (elimF D φ) (merge D ρ) ↔ Holds H.mem H.lt I φ ρ
  | .mem x y, ρ => by
    show H.mem (merge D ρ _) (merge D ρ _) ↔ H.mem (ρ x) (ρ y)
    rw [merge_zero, merge_zero]
  | .lt x y, ρ => by
    show H.lt (merge D ρ _) (merge D ρ _) ↔ H.lt (ρ x) (ρ y)
    rw [merge_zero, merge_zero]
  | .eq x y, ρ => by
    show merge D ρ _ = merge D ρ _ ↔ ρ x = ρ y
    rw [merge_zero, merge_zero]
  | .rel k x y z, ρ => by
    have hxy : Nat.pair (k + 1) (D.x k) ≠ Nat.pair (k + 1) (D.y k) :=
      fun e => D.xy k (pair_inj_right _ e)
    have hxz : Nat.pair (k + 1) (D.x k) ≠ Nat.pair (k + 1) (D.z k) :=
      fun e => D.xz k (pair_inj_right _ e)
    have hyz : Nat.pair (k + 1) (D.y k) ≠ Nat.pair (k + 1) (D.z k) :=
      fun e => D.yz k (pair_inj_right _ e)
    have h0 : ∀ n n', Nat.pair 0 n ≠ Nat.pair (k + 1) n' :=
      fun n n' => pair_ne_of_fst (Nat.succ_ne_zero k).symm
    have key : ∀ a b c : H.W,
        (upd (upd (upd (merge D ρ) (Nat.pair (k + 1) (D.x k)) a) (Nat.pair (k + 1) (D.y k)) b)
          (Nat.pair (k + 1) (D.z k)) c) ∘ Nat.pair (k + 1) =
        upd (upd (upd (D.ρ k) (D.x k) a) (D.y k) b) (D.z k) c := by
      intro a b c
      rw [upd_comp _ (pair_inj_right _), upd_comp _ (pair_inj_right _),
        upd_comp _ (pair_inj_right _)]
      congr 3
      funext n
      exact merge_succ D ρ k n
    show (∃ a b c, (_ = _ ∧ _ = _ ∧ _ = _ ∧ _)) ↔ I k (ρ x) (ρ y) (ρ z)
    constructor
    · rintro ⟨a, b, c, e1, e2, e3, h⟩
      rw [upd_ne _ _ hxz, upd_ne _ _ hxy, upd_same, upd_ne _ _ (h0 _ _), upd_ne _ _ (h0 _ _),
        upd_ne _ _ (h0 _ _), merge_zero] at e1
      rw [upd_ne _ _ hyz, upd_same, upd_ne _ _ (h0 _ _), upd_ne _ _ (h0 _ _),
        upd_ne _ _ (h0 _ _), merge_zero] at e2
      rw [upd_same, upd_ne _ _ (h0 _ _), upd_ne _ _ (h0 _ _),
        upd_ne _ _ (h0 _ _), merge_zero] at e3
      rw [holds_map _ _ _ (pair_inj_right _), key] at h
      rw [← e1, ← e2, ← e3]
      exact (D.spec k a b c).mpr h
    · intro h
      refine ⟨ρ x, ρ y, ρ z, ?_, ?_, ?_, ?_⟩
      · rw [upd_ne _ _ hxz, upd_ne _ _ hxy, upd_same, upd_ne _ _ (h0 _ _), upd_ne _ _ (h0 _ _),
          upd_ne _ _ (h0 _ _), merge_zero]
      · rw [upd_ne _ _ hyz, upd_same, upd_ne _ _ (h0 _ _), upd_ne _ _ (h0 _ _),
          upd_ne _ _ (h0 _ _), merge_zero]
      · rw [upd_same, upd_ne _ _ (h0 _ _), upd_ne _ _ (h0 _ _),
          upd_ne _ _ (h0 _ _), merge_zero]
      · rw [holds_map _ _ _ (pair_inj_right _), key]
        exact (D.spec k _ _ _).mp h
  | .tru, _ => Iff.rfl
  | .fls, _ => Iff.rfl
  | .neg φ, ρ => not_congr (holds_elimF D φ ρ)
  | .and φ ψ, ρ => and_congr (holds_elimF D φ ρ) (holds_elimF D ψ ρ)
  | .or φ ψ, ρ => or_congr (holds_elimF D φ ρ) (holds_elimF D ψ ρ)
  | .imp φ ψ, ρ => imp_congr (holds_elimF D φ ρ) (holds_elimF D ψ ρ)
  | .iff φ ψ, ρ => iff_congr (holds_elimF D φ ρ) (holds_elimF D ψ ρ)
  | .all x φ, ρ => forall_congr' fun a => by
      rw [merge_upd]
      exact holds_elimF D φ (upd ρ x a)
  | .ex x φ, ρ => exists_congr fun a => by
      rw [merge_upd]
      exact holds_elimF D φ (upd ρ x a)

/-- A predicate given by a formula with additional definable symbols is definable. -/
theorem Def1.ofRel (P : H.W → Prop) (l : List (H.W → H.W → H.W → Prop)) (hl : AllDef3 H l)
    (φ : Form) (ρ : ℕ → H.W) (x : ℕ)
    (h : ∀ a, P a ↔ Holds H.mem H.lt (relAt l) φ (upd ρ x a)) : Def1 H P := by
  obtain ⟨D⟩ := exists_relData (def3_relAt H l hl)
  refine ⟨elimF D φ, merge D ρ, Nat.pair 0 x, pure_elimF D φ, fun a => ?_⟩
  rw [h a, merge_upd, holds_elimF]

theorem Def2.ofRel (R : H.W → H.W → Prop) (l : List (H.W → H.W → H.W → Prop)) (hl : AllDef3 H l)
    (φ : Form) (ρ : ℕ → H.W) (x y : ℕ) (hxy : x ≠ y)
    (h : ∀ a b, R a b ↔ Holds H.mem H.lt (relAt l) φ (upd (upd ρ x a) y b)) : Def2 H R := by
  obtain ⟨D⟩ := exists_relData (def3_relAt H l hl)
  refine ⟨elimF D φ, merge D ρ, Nat.pair 0 x, Nat.pair 0 y, pure_elimF D φ,
    fun e => hxy (pair_inj_right _ e), fun a b => ?_⟩
  rw [h a b, merge_upd, merge_upd, holds_elimF]

theorem Def3.ofRel (R : H.W → H.W → H.W → Prop) (l : List (H.W → H.W → H.W → Prop))
    (hl : AllDef3 H l) (φ : Form) (ρ : ℕ → H.W) (x y z : ℕ) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (h : ∀ a b c, R a b c ↔ Holds H.mem H.lt (relAt l) φ (upd (upd (upd ρ x a) y b) z c)) :
    Def3 H R := by
  obtain ⟨D⟩ := exists_relData (def3_relAt H l hl)
  refine ⟨elimF D φ, merge D ρ, Nat.pair 0 x, Nat.pair 0 y, Nat.pair 0 z, pure_elimF D φ,
    fun e => hxy (pair_inj_right _ e), fun e => hxz (pair_inj_right _ e),
    fun e => hyz (pair_inj_right _ e), fun a b c => ?_⟩
  rw [h a b c, merge_upd, merge_upd, merge_upd, holds_elimF]

theorem upd_comp_ne {W : Type} (e : ℕ → W) {f : ℕ → ℕ} {z : ℕ} (hz : ∀ n, f n ≠ z) (c : W) :
    (upd e z c) ∘ f = e ∘ f := by
  funext n
  simp [upd_ne _ _ (hz n)]

/-- A definable unary predicate as a ternary relation. -/
theorem Def1.pad {P : H.W → Prop} (h : Def1 H P) : Def3 H (fun a _ _ => P a) := by
  obtain ⟨φ, ρ, x, hφ, h⟩ := h
  refine ⟨φ.map (Nat.pair 1), fun m => ρ (Nat.unpair m).2, Nat.pair 1 x, Nat.pair 0 0,
    Nat.pair 0 1, Form.pure_map _ _ hφ, pair_ne_of_fst (by decide), pair_ne_of_fst (by decide),
    fun e => by simpa using pair_inj_right _ e, fun a b c => ?_⟩
  have hρ : (fun m => ρ (Nat.unpair m).2) ∘ Nat.pair 1 = ρ := by
    funext n
    simp [Nat.unpair_pair]
  show P a ↔ _
  rw [holds_map _ _ _ (pair_inj_right _),
    upd_comp_ne _ (fun n => pair_ne_of_fst (by decide)),
    upd_comp_ne _ (fun n => pair_ne_of_fst (by decide)), upd_comp _ (pair_inj_right _), hρ]
  exact h a

/-- A definable binary relation as a ternary relation. -/
theorem Def2.pad {R : H.W → H.W → Prop} (h : Def2 H R) : Def3 H (fun a b _ => R a b) := by
  obtain ⟨φ, ρ, x, y, hφ, hxy, h⟩ := h
  refine ⟨φ.map (Nat.pair 1), fun m => ρ (Nat.unpair m).2, Nat.pair 1 x, Nat.pair 1 y,
    Nat.pair 0 0, Form.pure_map _ _ hφ, fun e => hxy (pair_inj_right _ e),
    pair_ne_of_fst (by decide), pair_ne_of_fst (by decide), fun a b c => ?_⟩
  have hρ : (fun m => ρ (Nat.unpair m).2) ∘ Nat.pair 1 = ρ := by
    funext n
    simp [Nat.unpair_pair]
  show R a b ↔ _
  rw [holds_map _ _ _ (pair_inj_right _),
    upd_comp_ne _ (fun n => pair_ne_of_fst (by decide)), upd_comp _ (pair_inj_right _),
    upd_comp _ (pair_inj_right _), hρ]
  exact h a b

end elim

/-! ## The tactic `hdef` -/

namespace HostReify

open Lean Meta Elab Tactic

structure St where
  params : Array Expr := #[]
  flats : Array Name := #[]
  next : Nat := 1000

abbrev RM := StateT St MetaM

def fresh : RM Nat := do
  let s ← get
  set { s with next := s.next + 1 }
  return s.next

def dependsOn (bound : Array (Expr × Nat)) (e : Expr) : Bool :=
  e.hasAnyFVar (fun id => bound.any (fun p => p.1.fvarId! == id))

/-- The variable number of a parameter (a term that does not depend on the bound variables). -/
def paramOf (e : Expr) : RM Expr := do
  let s ← get
  for i in [0:s.params.size] do
    if s.params[i]! == e then return mkNatLit i
  modify fun s => { s with params := s.params.push e }
  return mkNatLit s.params.size

/-- Is `e` an application of one of the abstract relations? Returns its index and arguments. -/
def absApp? (abs : Array (Expr × Nat)) (e : Expr) : Option (Nat × Array Expr) := Id.run do
  let args := e.getAppArgs
  let fn := e.getAppFn
  for i in [0:abs.size] do
    let (P, ar) := abs[i]!
    if args.size ≥ ar then
      let head := mkAppN fn (args.extract 0 (args.size - ar))
      if head == P then
        return some (i, args.extract (args.size - ar) args.size)
  return none

mutual

/-- Give a variable to the term `e` and continue with `k`. If `e` is a bound variable or does
not depend on the bound variables, it gets its own variable. If `e` is `f t₁ … tₙ` for a function
`f` with a declared graph `f.graph`, a new variable `y` is bound by `∃ y, f.graph y t₁ … tₙ ∧ _`.
The continuation receives the variable number, the term standing for `e` in the flattened
statement, the term standing for `e` in the unfolded statement, and the bound variables. -/
partial def withTerm (H W : Expr) (abs : Array (Expr × Nat)) (bound : Array (Expr × Nat))
    (e : Expr) (k : Expr → Expr → Expr → Array (Expr × Nat) → RM (Expr × Expr × Expr)) :
    RM (Expr × Expr × Expr) := do
  let e ← instantiateMVars e
  for (x, n) in bound do
    if x == e then return ← k (mkNatLit n) e e bound
  if !dependsOn bound e then
    return ← k (← paramOf e) e e bound
  let fn := e.getAppFn
  let args := e.getAppArgs
  let some c := fn.constName? |
    throwError "hdef: the term{indentExpr e}\ndepends on a bound variable and is not an application of a function with a graph"
  let gname := c ++ `graph
  unless (← getEnv).contains gname do
    match ← unfoldDefinition? e with
    | some e' => return ← withTerm H W abs bound e'.headBeta k
    | none =>
      throwError "hdef: the term{indentExpr e}\ndepends on a bound variable and `{gname}` is not declared"
  -- the arguments after the host
  let targs := args.extract 1 args.size
  withTerms H W abs bound targs.toList #[] #[] fun fargs' targs' bound' => do
    withLocalDeclD `y W fun y => do
      let n ← fresh
      let bound'' := bound'.push (y, n)
      let gProp := mkAppN (mkConst gname) (#[H, y] ++ fargs')
      let (gForm, _, _) ← reify H W abs bound'' gProp
      let fl := c ++ `flat
      modify fun s => if s.flats.contains fl then s else { s with flats := s.flats.push fl }
      let tterm := mkAppN fn (#[H] ++ targs')
      let (bForm, bProp, bTerm) ← k (mkNatLit n) y tterm bound''
      let form := mkApp2 (mkConst ``Form.ex) (mkNatLit n) (mkApp2 (mkConst ``Form.and) gForm bForm)
      let prop ← mkAppM ``Exists #[← mkLambdaFVars #[y] (mkAnd gProp bProp)]
      return (form, prop, bTerm)

/-- `withTerm` for a list of terms. -/
partial def withTerms (H W : Expr) (abs : Array (Expr × Nat)) (bound : Array (Expr × Nat))
    (es : List Expr) (facc tacc : Array Expr)
    (k : Array Expr → Array Expr → Array (Expr × Nat) → RM (Expr × Expr × Expr)) :
    RM (Expr × Expr × Expr) :=
  match es with
  | [] => k facc tacc bound
  | e :: es => withTerm H W abs bound e fun _ e' t' bound' =>
      withTerms H W abs bound' es (facc.push e') (tacc.push t') k

/-- Turn a statement about elements of the host into a formula. Returns the formula, the
statement in which the terms that depend on bound variables have been replaced by variables
(the flattened statement), and the statement with all definitions unfolded but with the terms
kept (the unfolded statement). -/
partial def reify (H W : Expr) (abs : Array (Expr × Nat)) (bound : Array (Expr × Nat))
    (e : Expr) : RM (Expr × Expr × Expr) := do
  let e ← instantiateMVars e
  let e := e.headBeta
  if let some (k, args) := absApp? abs e then
    let fn := mkAppN e.getAppFn (e.getAppArgs.extract 0 (e.getAppNumArgs - args.size))
    return ← withTerm H W abs bound args[0]! fun x a a' bd =>
      if args.size == 1 then
        return (mkApp4 (mkConst ``Form.rel) (mkNatLit k) x x x, mkApp fn a, mkApp fn a')
      else withTerm H W abs bd args[1]! fun y b b' bd =>
        if args.size == 2 then
          return (mkApp4 (mkConst ``Form.rel) (mkNatLit k) x y x, mkApp2 fn a b, mkApp2 fn a' b')
        else withTerm H W abs bd args[2]! fun z c c' _ =>
          return (mkApp4 (mkConst ``Form.rel) (mkNatLit k) x y z, mkApp3 fn a b c,
            mkApp3 fn a' b' c')
  match_expr e with
  | And p q =>
    let (f1, p1, t1) ← reify H W abs bound p
    let (f2, p2, t2) ← reify H W abs bound q
    return (mkApp2 (mkConst ``Form.and) f1 f2, mkAnd p1 p2, mkAnd t1 t2)
  | Or p q =>
    let (f1, p1, t1) ← reify H W abs bound p
    let (f2, p2, t2) ← reify H W abs bound q
    return (mkApp2 (mkConst ``Form.or) f1 f2, mkOr p1 p2, mkOr t1 t2)
  | Iff p q =>
    let (f1, p1, t1) ← reify H W abs bound p
    let (f2, p2, t2) ← reify H W abs bound q
    return (mkApp2 (mkConst ``Form.iff) f1 f2, mkApp2 (mkConst ``Iff) p1 p2,
      mkApp2 (mkConst ``Iff) t1 t2)
  | Not p =>
    let (f1, p1, t1) ← reify H W abs bound p
    return (mkApp (mkConst ``Form.neg) f1, mkNot p1, mkNot t1)
  | True => return (mkConst ``Form.tru, e, e)
  | False => return (mkConst ``Form.fls, e, e)
  | Eq α a b =>
    unless ← isDefEq α W do
      throwError "hdef: equality at the type{indentExpr α}"
    let eq := mkConst ``Eq [Level.succ Level.zero]
    withTerm H W abs bound a fun x a' a'' bd => withTerm H W abs bd b fun y b' b'' _ =>
      return (mkApp2 (mkConst ``Form.eq) x y, mkApp3 eq W a' b', mkApp3 eq W a'' b'')
  | Ne α a b =>
    unless ← isDefEq α W do
      throwError "hdef: inequality at the type{indentExpr α}"
    let eq := mkConst ``Eq [Level.succ Level.zero]
    withTerm H W abs bound a fun x a' a'' bd => withTerm H W abs bd b fun y b' b'' _ =>
      return (mkApp (mkConst ``Form.neg) (mkApp2 (mkConst ``Form.eq) x y),
        mkNot (mkApp3 eq W a' b'), mkNot (mkApp3 eq W a'' b''))
  | Exists α f =>
    unless ← isDefEq α W do
      throwError "hdef: quantifier over the type{indentExpr α}"
    let n ← fresh
    withLocalDeclD `x W fun x => do
      let (φ, p, t) ← reify H W abs (bound.push (x, n)) (mkApp f x)
      return (mkApp2 (mkConst ``Form.ex) (mkNatLit n) φ,
        ← mkAppM ``Exists #[← mkLambdaFVars #[x] p], ← mkAppM ``Exists #[← mkLambdaFVars #[x] t])
  | Host.mem _ a b =>
    let mem := mkConst ``Host.mem
    withTerm H W abs bound a fun x a' a'' bd => withTerm H W abs bd b fun y b' b'' _ =>
      return (mkApp2 (mkConst ``Form.mem) x y, mkApp3 mem H a' b', mkApp3 mem H a'' b'')
  | Host.lt _ a b =>
    let lt := mkConst ``Host.lt
    withTerm H W abs bound a fun x a' a'' bd => withTerm H W abs bd b fun y b' b'' _ =>
      return (mkApp2 (mkConst ``Form.lt) x y, mkApp3 lt H a' b', mkApp3 lt H a'' b'')
  | Membership.mem _ _ _ s a =>
    let mem := mkConst ``Host.mem
    withTerm H W abs bound a fun x a' a'' bd => withTerm H W abs bd s fun y s' s'' _ =>
      return (mkApp2 (mkConst ``Form.mem) x y, mkApp3 mem H a' s', mkApp3 mem H a'' s'')
  | _ =>
    if e.isForall then
      let dom := e.bindingDomain!
      if !e.bindingBody!.hasLooseBVars && (← isProp dom) then
        let (f1, p1, t1) ← reify H W abs bound dom
        let (f2, p2, t2) ← reify H W abs bound e.bindingBody!
        return (mkApp2 (mkConst ``Form.imp) f1 f2, ← mkArrow p1 p2, ← mkArrow t1 t2)
      else
        unless ← isDefEq dom W do
          throwError "hdef: quantifier over the type{indentExpr dom}"
        let n ← fresh
        withLocalDeclD e.bindingName! W fun x => do
          let (φ, p, t) ← reify H W abs (bound.push (x, n)) (e.bindingBody!.instantiate1 x)
          return (mkApp2 (mkConst ``Form.all) (mkNatLit n) φ, ← mkForallFVars #[x] p,
            ← mkForallFVars #[x] t)
    else
      match ← unfoldDefinition? e with
      | some e' => reify H W abs bound e'
      | none =>
        let e' ← whnfCore e
        if e' != e then reify H W abs bound e'
        else throwError "hdef: cannot turn into a formula:{indentExpr e}"

end

/-- A list of expressions of the type `α`, as an expression. -/
def mkListE (α : Expr) (ps : Array Expr) : Expr := Id.run do
  let mut l := mkApp (mkConst ``List.nil [Level.zero]) α
  for p in ps.reverse do
    l := mkApp3 (mkConst ``List.cons [Level.zero]) α p l
  return l

/-- The abstract relations in the local context: hypotheses `Def1 H P`, `Def2 H R`, `Def3 H R`.
Returns the relation, its arity, the relation as a ternary one, and the proof that this is
definable. -/
def collectAbs (H W : Expr) : MetaM (Array (Expr × Nat × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    match_expr t with
    | Def1 H' P =>
      let P := P.eta
      if H' == H then
        let R3 ← withLocalDeclD `a W fun a => withLocalDeclD `b W fun b =>
          withLocalDeclD `c W fun c => mkLambdaFVars #[a, b, c] (mkApp P a)
        out := out.push (P, 1, R3, mkApp3 (mkConst ``Def1.pad) H P d.toExpr)
    | Def2 H' R =>
      let R := R.eta
      if H' == H then
        let R3 ← withLocalDeclD `a W fun a => withLocalDeclD `b W fun b =>
          withLocalDeclD `c W fun c => mkLambdaFVars #[a, b, c] (mkApp2 R a b)
        out := out.push (R, 2, R3, mkApp3 (mkConst ``Def2.pad) H R d.toExpr)
    | Def3 H' R =>
      let R := R.eta
      if H' == H then
        out := out.push (R, 3, R, d.toExpr)
    | _ => pure ()
  return out

/-- Close a goal `∀ a …, P a … ↔ Holds …`. The right-hand side is definitionally the flattened
statement `P' a …`; the flattening lemmas turn it into the unfolded statement `P'' a …`, which
is definitionally `P a …`. -/
def closeIff (n : Nat) (P' P'' : Expr) (flats : Array Name) : TacticM Unit := do
  let g ← getMainGoal
  let (xs, g) ← g.introNP n
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := t.iff? | throwError "hdef: internal error (not an iff)"
    let mid := (mkAppN P' (xs.map mkFVar)).headBeta
    let mid' := (mkAppN P'' (xs.map mkFVar)).headBeta
    let iff := mkConst ``Iff
    if flats.isEmpty then
      let g1 ← mkFreshExprSyntheticOpaqueMVar (mkApp2 iff lhs mid)
      let g2 ← mkFreshExprSyntheticOpaqueMVar (mkApp2 iff mid rhs)
      g.assign (← mkAppM ``Iff.trans #[g1, g2])
      replaceMainGoal [g1.mvarId!, g2.mvarId!]
      evalTactic (← `(tactic| exact Iff.rfl))
      evalTactic (← `(tactic| exact Iff.rfl))
    else
      let g1 ← mkFreshExprSyntheticOpaqueMVar (mkApp2 iff lhs mid')
      let g2 ← mkFreshExprSyntheticOpaqueMVar (mkApp2 iff mid' mid)
      let g3 ← mkFreshExprSyntheticOpaqueMVar (mkApp2 iff mid rhs)
      g.assign (← mkAppM ``Iff.trans #[g1, ← mkAppM ``Iff.trans #[g2, g3]])
      replaceMainGoal [g1.mvarId!, g3.mvarId!, g2.mvarId!]
      evalTactic (← `(tactic| exact Iff.rfl))
      evalTactic (← `(tactic| exact Iff.rfl))
      let ids := flats.map fun n => mkIdent n
      evalTactic (← `(tactic| simp (config := { maxSteps := 100000000 }) only [$[$ids:ident],*]))

/-- `hdef` proves goals of the form `Def1 H P`, `Def2 H R` and `Def3 H R`. The predicate may
mention relations for which a hypothesis `Def1 H _`, `Def2 H _` or `Def3 H _` is in the
context, and terms `f t₁ … tₙ` for functions `f` with a declared graph `f.graph` and flattening
lemma `f.flat`. -/
elab "hdef" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let (H, P, ar) ← match_expr t with
    | Def1 H P => pure (H, P, 1)
    | Def2 H P => pure (H, P, 2)
    | Def3 H P => pure (H, P, 3)
    | _ => throwError "hdef: the goal is not of the form `Def1 H P`, `Def2 H R` or `Def3 H R`"
  let W := mkApp (mkConst ``Host.W) H
  let absAll ← collectAbs H W
  let abs := absAll.map fun (P, n, _, _) => (P, n)
  let relTy ← mkArrow W (← mkArrow W (← mkArrow W (mkSort Level.zero)))
  let l := mkListE relTy (absAll.map fun (_, _, R3, _) => R3)
  let mut hl := mkConst ``True.intro
  for (_, _, _, pf) in absAll.reverse do
    hl ← mkAppM ``And.intro #[pf, hl]
  let dflt := mkApp (mkConst ``Host.dflt) H
  if ar == 1 then
    let ((φ, P', P''), st) ← (withLocalDeclD `a W fun a => do
      let (φ, p, t) ← reify H W abs #[(a, 999)] (mkApp P a)
      return (φ, ← mkLambdaFVars #[a] p, ← mkLambdaFVars #[a] t)).run {}
    let ρ := mkApp3 (mkConst ``env) W dflt (mkListE W st.params)
    let pf := mkAppN (mkConst ``Def1.ofRel) #[H, P, l, hl, φ, ρ, mkNatLit 999]
    replaceMainGoal (← g.apply pf)
    closeIff 1 P' P'' st.flats
  else if ar == 2 then
    let ((φ, P', P''), st) ← (withLocalDeclD `a W fun a => withLocalDeclD `b W fun b => do
      let (φ, p, t) ← reify H W abs #[(a, 998), (b, 999)] (mkApp2 P a b)
      return (φ, ← mkLambdaFVars #[a, b] p, ← mkLambdaFVars #[a, b] t)).run {}
    let ρ := mkApp3 (mkConst ``env) W dflt (mkListE W st.params)
    let ne ← mkDecideProof (← mkAppM ``Ne #[mkNatLit 998, mkNatLit 999])
    let pf := mkAppN (mkConst ``Def2.ofRel) #[H, P, l, hl, φ, ρ, mkNatLit 998, mkNatLit 999, ne]
    replaceMainGoal (← g.apply pf)
    closeIff 2 P' P'' st.flats
  else
    let ((φ, P', P''), st) ← (withLocalDeclD `a W fun a => withLocalDeclD `b W fun b =>
      withLocalDeclD `c W fun c => do
        let (φ, p, t) ← reify H W abs #[(a, 997), (b, 998), (c, 999)] (mkApp3 P a b c)
        return (φ, ← mkLambdaFVars #[a, b, c] p, ← mkLambdaFVars #[a, b, c] t)).run {}
    let ρ := mkApp3 (mkConst ``env) W dflt (mkListE W st.params)
    let ne1 ← mkDecideProof (← mkAppM ``Ne #[mkNatLit 997, mkNatLit 998])
    let ne2 ← mkDecideProof (← mkAppM ``Ne #[mkNatLit 997, mkNatLit 999])
    let ne3 ← mkDecideProof (← mkAppM ``Ne #[mkNatLit 998, mkNatLit 999])
    let pf := mkAppN (mkConst ``Def3.ofRel)
      #[H, P, l, hl, φ, ρ, mkNatLit 997, mkNatLit 998, mkNatLit 999, ne1, ne2, ne3]
    replaceMainGoal (← g.apply pf)
    closeIff 3 P' P'' st.flats

end HostReify


/-! ## Basic set theory in a host -/

namespace Host

variable (H : Host)

theorem ext' {x y : H.W} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := H.ext x y h

/-- Separation for a definable predicate. -/
theorem sep' (a : H.W) (P : H.W → Prop) (hP : Def1 H P) :
    ∃ b : H.W, ∀ y, y ∈ b ↔ y ∈ a ∧ P y := by
  obtain ⟨φ, ρ, x, hφ, h⟩ := hP
  obtain ⟨b, hb⟩ := H.sep φ hφ ρ x a
  exact ⟨b, fun y => by rw [h y]; exact hb y⟩

/-- Collection for a definable relation. -/
theorem coll' (a : H.W) (R : H.W → H.W → Prop) (hR : Def2 H R) (h : ∀ u ∈ a, ∃ v, R u v) :
    ∃ b : H.W, ∀ u ∈ a, ∃ v ∈ b, R u v := by
  obtain ⟨φ, ρ, x, y, hφ, -, hφR⟩ := hR
  obtain ⟨b, hb⟩ := H.coll φ hφ ρ x y a (fun u hu => by
    obtain ⟨v, hv⟩ := h u hu
    exact ⟨v, (hφR u v).mp hv⟩)
  exact ⟨b, fun u hu => by
    obtain ⟨v, hvb, hv⟩ := hb u hu
    exact ⟨v, hvb, (hφR u v).mpr hv⟩⟩

/-- Every definable predicate that holds somewhere has a least element at which it holds. -/
theorem least' (P : H.W → Prop) (hP : Def1 H P) {a : H.W} (ha : P a) :
    ∃ m, P m ∧ ∀ b, H.lt b m → ¬ P b := by
  obtain ⟨φ, ρ, x, hφ, h⟩ := hP
  obtain ⟨m, hm, hmin⟩ := H.lt_least φ hφ ρ x a ((h a).mp ha)
  exact ⟨m, (h m).mpr hm, fun b hb hPb => hmin b hb ((h b).mp hPb)⟩

/-- Induction on membership for a definable predicate. -/
theorem ind' (P : H.W → Prop) (hP : Def1 H P) (h : ∀ a, (∀ b ∈ a, P b) → P a) : ∀ a, P a := by
  intro a
  by_contra hna
  obtain ⟨m, hm, hmin⟩ := H.least' (fun x => ¬ P x) (by hdef) hna
  exact hm (h m fun b hb => not_not.mp (hmin b (H.mem_lt b m hb)))

theorem mem_irrefl (x : H.W) : ¬ x ∈ x := fun h => H.lt_irrefl x (H.mem_lt x x h)

theorem mem_asymm {x y : H.W} (h : x ∈ y) : ¬ y ∈ x :=
  fun h' => H.lt_irrefl x (H.lt_trans x y x (H.mem_lt x y h) (H.mem_lt y x h'))

/-- The set of the members of `a` that satisfy `P`. -/
noncomputable def sepS (a : H.W) (P : H.W → Prop) (hP : Def1 H P) : H.W :=
  Classical.choose (H.sep' a P hP)

theorem mem_sepS {a : H.W} {P : H.W → Prop} {hP : Def1 H P} {y : H.W} :
    y ∈ H.sepS a P hP ↔ y ∈ a ∧ P y :=
  Classical.choose_spec (H.sep' a P hP) y

/-- The empty set. -/
noncomputable def emp : H.W := H.sepS H.dflt (fun _ => False) (by hdef)

theorem not_mem_emp (x : H.W) : ¬ x ∈ H.emp := fun h => (H.mem_sepS.mp h).2

theorem eq_emp {x : H.W} (h : ∀ z, ¬ z ∈ x) : x = H.emp :=
  H.ext' fun z => ⟨fun hz => (h z hz).elim, fun hz => (H.not_mem_emp z hz).elim⟩

theorem ne_emp {x : H.W} (h : x ≠ H.emp) : ∃ z, z ∈ x := by
  by_contra hn
  exact h (H.eq_emp fun z hz => hn ⟨z, hz⟩)

/-- The unordered pair. -/
noncomputable def up (a b : H.W) : H.W := Classical.choose (H.pair a b)

theorem mem_up {a b z : H.W} : z ∈ H.up a b ↔ z = a ∨ z = b :=
  Classical.choose_spec (H.pair a b) z

/-- The singleton. -/
noncomputable def sg (a : H.W) : H.W := H.up a a

theorem mem_sg {a z : H.W} : z ∈ H.sg a ↔ z = a := by
  show z ∈ H.up a a ↔ _
  rw [mem_up, or_self]

theorem sg_inj {a b : H.W} (h : H.sg a = H.sg b) : a = b := by
  have : a ∈ H.sg b := by rw [← h]; exact H.mem_sg.mpr rfl
  exact H.mem_sg.mp this

theorem up_eq_sg {a b c : H.W} (h : H.up a b = H.sg c) : a = c ∧ b = c := by
  have h1 : a ∈ H.sg c := by rw [← h]; exact H.mem_up.mpr (Or.inl rfl)
  have h2 : b ∈ H.sg c := by rw [← h]; exact H.mem_up.mpr (Or.inr rfl)
  exact ⟨H.mem_sg.mp h1, H.mem_sg.mp h2⟩

/-- The ordered pair. -/
noncomputable def op (a b : H.W) : H.W := H.up (H.sg a) (H.up a b)

theorem op_inj {a b c d : H.W} (h : H.op a b = H.op c d) : a = c ∧ b = d := by
  have h1 : H.sg a ∈ H.op c d := by rw [← h]; exact H.mem_up.mpr (Or.inl rfl)
  have h2 : H.up a b ∈ H.op c d := by rw [← h]; exact H.mem_up.mpr (Or.inr rfl)
  have h3 : H.up c d ∈ H.op a b := by rw [h]; exact H.mem_up.mpr (Or.inr rfl)
  have hac : a = c := by
    rcases H.mem_up.mp h1 with e | e
    · exact H.sg_inj e
    · exact (H.up_eq_sg e.symm).1.symm
  subst hac
  refine ⟨rfl, ?_⟩
  rcases H.mem_up.mp h2 with e | e
  · have hb : b = a := (H.up_eq_sg e).2
    rcases H.mem_up.mp h3 with e' | e'
    · have hd : d = a := (H.up_eq_sg e').2
      rw [hb, hd]
    · have hd : d ∈ H.up a b := by rw [← e']; exact H.mem_up.mpr (Or.inr rfl)
      rcases H.mem_up.mp hd with e'' | e''
      · rw [hb, e'']
      · exact e''.symm
  · have hb : b ∈ H.up a d := by rw [← e]; exact H.mem_up.mpr (Or.inr rfl)
    rcases H.mem_up.mp hb with e' | e'
    · have hd : d ∈ H.up a b := by rw [e]; exact H.mem_up.mpr (Or.inr rfl)
      rcases H.mem_up.mp hd with e'' | e''
      · rw [e', e'']
      · exact e''.symm
    · exact e'

/-- `p` is the unordered pair of `a` and `b`. -/
def IsUp (p a b : H.W) : Prop := ∀ z, z ∈ p ↔ z = a ∨ z = b

theorem isUp_iff {p a b : H.W} : H.IsUp p a b ↔ p = H.up a b :=
  ⟨fun h => H.ext' fun z => (h z).trans H.mem_up.symm, fun h z => by rw [h]; exact H.mem_up⟩

/-- `p` is the ordered pair of `a` and `b`. -/
def IsOp (p a b : H.W) : Prop := ∃ s u, H.IsUp s a a ∧ H.IsUp u a b ∧ H.IsUp p s u

theorem isOp_iff {p a b : H.W} : H.IsOp p a b ↔ p = H.op a b := by
  constructor
  · rintro ⟨s, u, hs, hu, hp⟩
    rw [H.isUp_iff.mp hs, H.isUp_iff.mp hu] at hp
    exact H.isUp_iff.mp hp
  · intro h
    exact ⟨H.sg a, H.up a b, H.isUp_iff.mpr rfl, H.isUp_iff.mpr rfl, H.isUp_iff.mpr h⟩

theorem isOp_op (a b : H.W) : H.IsOp (H.op a b) a b := H.isOp_iff.mpr rfl

/-- The pair of `a` and `b` belongs to `f`. -/
def App (f a b : H.W) : Prop := ∃ p, H.IsOp p a b ∧ p ∈ f

theorem app_iff {f a b : H.W} : H.App f a b ↔ H.op a b ∈ f := by
  constructor
  · rintro ⟨p, hp, hpf⟩
    rw [← H.isOp_iff.mp hp]
    exact hpf
  · intro h
    exact ⟨_, H.isOp_op a b, h⟩

/-- The union of a set. -/
noncomputable def un (x : H.W) : H.W := Classical.choose (H.union x)

theorem mem_un {x z : H.W} : z ∈ H.un x ↔ ∃ y, y ∈ x ∧ z ∈ y :=
  Classical.choose_spec (H.union x) z

/-- The union of two sets. -/
noncomputable def bun (a b : H.W) : H.W := H.un (H.up a b)

theorem mem_bun {a b z : H.W} : z ∈ H.bun a b ↔ z ∈ a ∨ z ∈ b := by
  show z ∈ H.un (H.up a b) ↔ _
  rw [mem_un]
  constructor
  · rintro ⟨y, hy, hz⟩
    rcases H.mem_up.mp hy with e | e
    · exact Or.inl (e ▸ hz)
    · exact Or.inr (e ▸ hz)
  · rintro (h | h)
    · exact ⟨a, H.mem_up.mpr (Or.inl rfl), h⟩
    · exact ⟨b, H.mem_up.mpr (Or.inr rfl), h⟩

/-- The successor `x ∪ {x}`. -/
noncomputable def suc (x : H.W) : H.W := H.bun x (H.sg x)

theorem mem_suc {x z : H.W} : z ∈ H.suc x ↔ z ∈ x ∨ z = x := by
  show z ∈ H.bun x (H.sg x) ↔ _
  rw [mem_bun, mem_sg]

/-- Inclusion. -/
def Sub (x y : H.W) : Prop := ∀ z, z ∈ x → z ∈ y

theorem sub_antisymm {x y : H.W} (h1 : H.Sub x y) (h2 : H.Sub y x) : x = y :=
  H.ext' fun z => ⟨h1 z, h2 z⟩

/-- Replacement for a definable relation that is functional on `a`. -/
theorem repl' (a : H.W) (R : H.W → H.W → Prop) (hR : Def2 H R)
    (hfun : ∀ u ∈ a, ∀ v v', R u v → R u v' → v = v') :
    ∃ b : H.W, ∀ v, v ∈ b ↔ ∃ u ∈ a, R u v := by
  obtain ⟨a', ha'⟩ := H.sep' a (fun u => ∃ v, R u v) (by hdef)
  obtain ⟨b0, hb0⟩ := H.coll' a' R hR (fun u hu => ((ha' u).mp hu).2)
  obtain ⟨b, hb⟩ := H.sep' b0 (fun v => ∃ u, u ∈ a ∧ R u v) (by hdef)
  refine ⟨b, fun v => ⟨fun hv => ((hb v).mp hv).2, ?_⟩⟩
  rintro ⟨u, hu, huv⟩
  refine (hb v).mpr ⟨?_, u, hu, huv⟩
  obtain ⟨v', hv'b, hv'⟩ := hb0 u ((ha' u).mpr ⟨hu, v, huv⟩)
  rw [hfun u hu v v' huv hv']
  exact hv'b

/-- The image of `a` under a definable relation that is functional on `a`. -/
noncomputable def img (a : H.W) (R : H.W → H.W → Prop) (hR : Def2 H R)
    (hfun : ∀ u ∈ a, ∀ v v', R u v → R u v' → v = v') : H.W :=
  Classical.choose (H.repl' a R hR hfun)

theorem mem_img {a : H.W} {R : H.W → H.W → Prop} {hR : Def2 H R}
    {hfun : ∀ u ∈ a, ∀ v v', R u v → R u v' → v = v'} {v : H.W} :
    v ∈ H.img a R hR hfun ↔ ∃ u ∈ a, R u v :=
  Classical.choose_spec (H.repl' a R hR hfun) v

/-- The graph on `a` of a definable relation that is functional on `a`. -/
theorem graph' (a : H.W) (R : H.W → H.W → Prop) (hR : Def2 H R)
    (hfun : ∀ u ∈ a, ∀ v v', R u v → R u v' → v = v') :
    ∃ f : H.W, ∀ p, p ∈ f ↔ ∃ u v, u ∈ a ∧ R u v ∧ H.IsOp p u v := by
  obtain ⟨f, hf⟩ := H.repl' a (fun u p => ∃ v, R u v ∧ H.IsOp p u v) (by hdef)
    (fun u hu p p' ⟨v, hv, hp⟩ ⟨v', hv', hp'⟩ => by
      rw [H.isOp_iff.mp hp, H.isOp_iff.mp hp', hfun u hu v v' hv hv'])
  refine ⟨f, fun p => (hf p).trans ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu, v, hv, hp⟩
    exact ⟨u, v, hu, hv, hp⟩
  · rintro ⟨u, v, hu, hv, hp⟩
    exact ⟨u, hu, v, hv, hp⟩

/-- The product of two sets. -/
theorem prod' (a b : H.W) : ∃ c : H.W, ∀ p, p ∈ c ↔ ∃ u v, u ∈ a ∧ v ∈ b ∧ H.IsOp p u v := by
  have h1 : ∀ u : H.W, ∃ s : H.W, ∀ p, p ∈ s ↔ ∃ v, v ∈ b ∧ H.IsOp p u v := by
    intro u
    obtain ⟨s, hs⟩ := H.repl' b (fun v p => H.IsOp p u v) (by hdef)
      (fun v _ p p' hp hp' => by rw [H.isOp_iff.mp hp, H.isOp_iff.mp hp'])
    exact ⟨s, fun p => (hs p).trans ⟨fun ⟨v, hv, hp⟩ => ⟨v, hv, hp⟩, fun ⟨v, hv, hp⟩ => ⟨v, hv, hp⟩⟩⟩
  obtain ⟨t, ht⟩ := H.repl' a (fun u s => ∀ p, p ∈ s ↔ ∃ v, v ∈ b ∧ H.IsOp p u v) (by hdef)
    (fun u _ s s' hs hs' => H.ext' fun p => (hs p).trans (hs' p).symm)
  refine ⟨H.un t, fun p => H.mem_un.trans ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hp⟩
    obtain ⟨u, hu, hus⟩ := (ht s).mp hs
    obtain ⟨v, hv, hpv⟩ := (hus p).mp hp
    exact ⟨u, v, hu, hv, hpv⟩
  · rintro ⟨u, v, hu, hv, hp⟩
    obtain ⟨s, hs⟩ := h1 u
    exact ⟨s, (ht s).mpr ⟨u, hu, hs⟩, (hs p).mpr ⟨v, hv, hp⟩⟩

/-- The product of two sets. -/
noncomputable def prod (a b : H.W) : H.W := Classical.choose (H.prod' a b)

theorem mem_prod {a b p : H.W} : p ∈ H.prod a b ↔ ∃ u v, u ∈ a ∧ v ∈ b ∧ p = H.op u v := by
  refine (Classical.choose_spec (H.prod' a b) p).trans ?_
  constructor
  · rintro ⟨u, v, hu, hv, hp⟩
    exact ⟨u, v, hu, hv, H.isOp_iff.mp hp⟩
  · rintro ⟨u, v, hu, hv, hp⟩
    exact ⟨u, v, hu, hv, H.isOp_iff.mpr hp⟩

theorem op_mem_prod {a b u v : H.W} : H.op u v ∈ H.prod a b ↔ u ∈ a ∧ v ∈ b := by
  rw [mem_prod]
  constructor
  · rintro ⟨u', v', hu, hv, e⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    rw [e1, e2]
    exact ⟨hu, hv⟩
  · rintro ⟨hu, hv⟩
    exact ⟨u, v, hu, hv, rfl⟩

end Host


/-! ## Graphs of the basic operations, for the tactic `hdef` -/

namespace Host

variable (H : Host)

def up.graph (H : Host) (y a b : H.W) : Prop := H.IsUp y a b

theorem up.flat (H : Host) (a b : H.W) (Q : H.W → Prop) :
    (∃ y, Host.up.graph H y a b ∧ Q y) ↔ Q (H.up a b) :=
  ⟨fun ⟨_, hy, hQ⟩ => (H.isUp_iff.mp hy) ▸ hQ, fun h => ⟨_, H.isUp_iff.mpr rfl, h⟩⟩

def sg.graph (H : Host) (y a : H.W) : Prop := H.IsUp y a a

theorem sg.flat (H : Host) (a : H.W) (Q : H.W → Prop) :
    (∃ y, Host.sg.graph H y a ∧ Q y) ↔ Q (H.sg a) :=
  ⟨fun ⟨_, hy, hQ⟩ => (show _ = H.sg a from H.isUp_iff.mp hy) ▸ hQ,
    fun h => ⟨_, H.isUp_iff.mpr rfl, h⟩⟩

def op.graph (H : Host) (y a b : H.W) : Prop := H.IsOp y a b

theorem op.flat (H : Host) (a b : H.W) (Q : H.W → Prop) :
    (∃ y, Host.op.graph H y a b ∧ Q y) ↔ Q (H.op a b) :=
  ⟨fun ⟨_, hy, hQ⟩ => (H.isOp_iff.mp hy) ▸ hQ, fun h => ⟨_, H.isOp_op a b, h⟩⟩

def un.graph (H : Host) (y x : H.W) : Prop := ∀ z, z ∈ y ↔ ∃ w, w ∈ x ∧ z ∈ w

theorem un.flat (H : Host) (x : H.W) (Q : H.W → Prop) :
    (∃ y, Host.un.graph H y x ∧ Q y) ↔ Q (H.un x) :=
  ⟨fun ⟨y, hy, hQ⟩ => (H.ext' fun z => (hy z).trans H.mem_un.symm : y = H.un x) ▸ hQ,
    fun h => ⟨_, fun _ => H.mem_un, h⟩⟩

def bun.graph (H : Host) (y a b : H.W) : Prop := ∀ z, z ∈ y ↔ z ∈ a ∨ z ∈ b

theorem bun.flat (H : Host) (a b : H.W) (Q : H.W → Prop) :
    (∃ y, Host.bun.graph H y a b ∧ Q y) ↔ Q (H.bun a b) :=
  ⟨fun ⟨y, hy, hQ⟩ => (H.ext' fun z => (hy z).trans H.mem_bun.symm : y = H.bun a b) ▸ hQ,
    fun h => ⟨_, fun _ => H.mem_bun, h⟩⟩

def suc.graph (H : Host) (y x : H.W) : Prop := ∀ z, z ∈ y ↔ z ∈ x ∨ z = x

theorem suc.flat (H : Host) (x : H.W) (Q : H.W → Prop) :
    (∃ y, Host.suc.graph H y x ∧ Q y) ↔ Q (H.suc x) :=
  ⟨fun ⟨y, hy, hQ⟩ => (H.ext' fun z => (hy z).trans H.mem_suc.symm : y = H.suc x) ▸ hQ,
    fun h => ⟨_, fun _ => H.mem_suc, h⟩⟩

example (c : H.W) : Def1 H (fun f => ∀ a b, H.op a b ∈ f → H.op b (H.suc a) ∈ f ∨ H.sg a = c) := by
  hdef

example (R : H.W → H.W → Prop) (hR : Def2 H R) :
    Def2 H (fun x y => ∃ z, R (H.op x z) (H.up y y) ∧ H.un z ≠ H.emp) := by
  hdef



end Host


/-! ## Functions and the natural numbers of a host -/

namespace Host

variable (H : Host)

theorem lt_op_left (a b : H.W) : H.lt a (H.op a b) :=
  H.lt_trans _ _ _ (H.mem_lt _ _ (H.mem_sg.mpr rfl)) (H.mem_lt _ _ (H.mem_up.mpr (Or.inl rfl)))

theorem lt_op_right (a b : H.W) : H.lt b (H.op a b) :=
  H.lt_trans _ _ _ (H.mem_lt _ _ (H.mem_up.mpr (Or.inr rfl))) (H.mem_lt _ _ (H.mem_up.mpr (Or.inr rfl)))

theorem lt_asymm {x y : H.W} (h : H.lt x y) : ¬ H.lt y x :=
  fun h' => H.lt_irrefl x (H.lt_trans x y x h h')

theorem lt_ne {x y : H.W} (h : H.lt x y) : x ≠ y := fun e => H.lt_irrefl x (e ▸ h)

/-- `f` is a function (a set of ordered pairs with at most one value at each argument). -/
def IsFun (f : H.W) : Prop :=
  (∀ p, p ∈ f → ∃ a b, H.IsOp p a b) ∧ ∀ a b b', H.App f a b → H.App f a b' → b = b'

/-- `d` is the domain of `f`. -/
def DomIs (f d : H.W) : Prop := ∀ a, a ∈ d ↔ ∃ b, H.App f a b

/-- `f` is a function with domain `d`. -/
def FunOn (f d : H.W) : Prop := H.IsFun f ∧ H.DomIs f d

/-- All values of `f` lie in `X`. -/
def RanSub (f X : H.W) : Prop := ∀ a b, H.App f a b → b ∈ X

theorem app_lt_left {f a b : H.W} (h : H.App f a b) : H.lt a f :=
  H.lt_trans _ _ _ (H.lt_op_left a b) (H.mem_lt _ _ (H.app_iff.mp h))

theorem app_lt_right {f a b : H.W} (h : H.App f a b) : H.lt b f :=
  H.lt_trans _ _ _ (H.lt_op_right a b) (H.mem_lt _ _ (H.app_iff.mp h))

theorem app_mem_unun_left {f a b : H.W} (h : H.App f a b) : a ∈ H.un (H.un f) :=
  H.mem_un.mpr ⟨H.sg a, H.mem_un.mpr ⟨H.op a b, H.app_iff.mp h, H.mem_up.mpr (Or.inl rfl)⟩,
    H.mem_sg.mpr rfl⟩

theorem app_mem_unun_right {f a b : H.W} (h : H.App f a b) : b ∈ H.un (H.un f) :=
  H.mem_un.mpr ⟨H.up a b, H.mem_un.mpr ⟨H.op a b, H.app_iff.mp h, H.mem_up.mpr (Or.inr rfl)⟩,
    H.mem_up.mpr (Or.inr rfl)⟩

/-- The domain of a set of pairs. -/
noncomputable def dom (f : H.W) : H.W := H.sepS (H.un (H.un f)) (fun a => ∃ b, H.App f a b) (by hdef)

theorem mem_dom {f a : H.W} : a ∈ H.dom f ↔ ∃ b, H.App f a b :=
  H.mem_sepS.trans ⟨fun h => h.2, fun ⟨b, hb⟩ => ⟨H.app_mem_unun_left hb, b, hb⟩⟩

/-- The range of a set of pairs. -/
noncomputable def ran (f : H.W) : H.W := H.sepS (H.un (H.un f)) (fun b => ∃ a, H.App f a b) (by hdef)

theorem mem_ran {f b : H.W} : b ∈ H.ran f ↔ ∃ a, H.App f a b :=
  H.mem_sepS.trans ⟨fun h => h.2, fun ⟨a, ha⟩ => ⟨H.app_mem_unun_right ha, a, ha⟩⟩

theorem domIs_dom (f : H.W) : H.DomIs f (H.dom f) := fun _ => H.mem_dom

theorem domIs_unique {f d d' : H.W} (h : H.DomIs f d) (h' : H.DomIs f d') : d = d' :=
  H.ext' fun a => (h a).trans (h' a).symm

/-- The function on `a` given by a definable relation that is functional on `a`. -/
noncomputable def mkFun (a : H.W) (R : H.W → H.W → Prop) (hR : Def2 H R)
    (hfun : ∀ u ∈ a, ∀ v v', R u v → R u v' → v = v') : H.W :=
  Classical.choose (H.graph' a R hR hfun)

theorem app_mkFun {a : H.W} {R : H.W → H.W → Prop} {hR : Def2 H R}
    {hfun : ∀ u ∈ a, ∀ v v', R u v → R u v' → v = v'} {u v : H.W} :
    H.App (H.mkFun a R hR hfun) u v ↔ u ∈ a ∧ R u v := by
  rw [app_iff]
  refine (Classical.choose_spec (H.graph' a R hR hfun) _).trans ⟨?_, ?_⟩
  · rintro ⟨u', v', hu, hv, hp⟩
    obtain ⟨e1, e2⟩ := H.op_inj (H.isOp_iff.mp hp)
    rw [e1, e2]
    exact ⟨hu, hv⟩
  · rintro ⟨hu, hv⟩
    exact ⟨u, v, hu, hv, H.isOp_op u v⟩

theorem isFun_mkFun {a : H.W} {R : H.W → H.W → Prop} {hR : Def2 H R}
    {hfun : ∀ u ∈ a, ∀ v v', R u v → R u v' → v = v'} : H.IsFun (H.mkFun a R hR hfun) := by
  constructor
  · intro p hp
    obtain ⟨u, v, -, -, h⟩ := (Classical.choose_spec (H.graph' a R hR hfun) p).mp hp
    exact ⟨u, v, h⟩
  · intro u v v' h h'
    obtain ⟨hu, hv⟩ := H.app_mkFun.mp h
    exact hfun u hu v v' hv (H.app_mkFun.mp h').2

/-! ### The natural numbers -/

/-- `e` has no members. -/
def IsEmp (e : H.W) : Prop := ∀ z, ¬ z ∈ e

theorem isEmp_iff {e : H.W} : H.IsEmp e ↔ e = H.emp :=
  ⟨fun h => H.eq_emp h, fun h => h ▸ H.not_mem_emp⟩

/-- `s` is the successor of `x`. -/
def IsSuc (s x : H.W) : Prop := ∀ z, z ∈ s ↔ z ∈ x ∨ z = x

theorem isSuc_iff {s x : H.W} : H.IsSuc s x ↔ s = H.suc x :=
  ⟨fun h => H.ext' fun z => (h z).trans H.mem_suc.symm, fun h z => by rw [h]; exact H.mem_suc⟩

/-- `w` contains the empty set and is closed under successor. -/
def Ind (w : H.W) : Prop :=
  (∃ e, e ∈ w ∧ H.IsEmp e) ∧ ∀ x, x ∈ w → ∃ s, s ∈ w ∧ H.IsSuc s x

theorem ind_iff {w : H.W} : H.Ind w ↔ H.emp ∈ w ∧ ∀ x, x ∈ w → H.suc x ∈ w := by
  constructor
  · rintro ⟨⟨e, he, he0⟩, h⟩
    refine ⟨by rw [← H.isEmp_iff.mp he0]; exact he, fun x hx => ?_⟩
    obtain ⟨s, hs, hsx⟩ := h x hx
    rw [← H.isSuc_iff.mp hsx]
    exact hs
  · rintro ⟨h0, h⟩
    exact ⟨⟨H.emp, h0, H.isEmp_iff.mpr rfl⟩, fun x hx => ⟨H.suc x, h x hx, H.isSuc_iff.mpr rfl⟩⟩

theorem exists_ind : ∃ w : H.W, H.Ind w := by
  obtain ⟨w, ⟨e, he, he0⟩, h⟩ := H.inf
  exact ⟨w, ⟨e, he, he0⟩, h⟩

/-- The set of the natural numbers. -/
noncomputable def om : H.W :=
  H.sepS (Classical.choose H.exists_ind) (fun n => ∀ w, H.Ind w → n ∈ w) (by hdef)

theorem mem_om {n : H.W} : n ∈ H.om ↔ ∀ w, H.Ind w → n ∈ w :=
  H.mem_sepS.trans ⟨fun h => h.2, fun h => ⟨h _ (Classical.choose_spec H.exists_ind), h⟩⟩

theorem emp_mem_om : H.emp ∈ H.om := H.mem_om.mpr fun _ hw => (H.ind_iff.mp hw).1

theorem suc_mem_om {n : H.W} (h : n ∈ H.om) : H.suc n ∈ H.om :=
  H.mem_om.mpr fun w hw => (H.ind_iff.mp hw).2 n (H.mem_om.mp h w hw)

/-- Induction on the natural numbers for a definable predicate. -/
theorem om_ind (P : H.W → Prop) (hP : Def1 H P) (h0 : P H.emp)
    (hs : ∀ n, n ∈ H.om → P n → P (H.suc n)) : ∀ n, n ∈ H.om → P n := by
  obtain ⟨w, hw⟩ := H.sep' H.om P hP
  have hind : H.Ind w := H.ind_iff.mpr
    ⟨(hw _).mpr ⟨H.emp_mem_om, h0⟩, fun x hx =>
      (hw _).mpr ⟨H.suc_mem_om ((hw x).mp hx).1, hs x ((hw x).mp hx).1 ((hw x).mp hx).2⟩⟩
  exact fun n hn => ((hw n).mp (H.mem_om.mp hn w hind)).2

theorem om_cases {n : H.W} (h : n ∈ H.om) : n = H.emp ∨ ∃ m, m ∈ H.om ∧ n = H.suc m :=
  H.om_ind (fun n => n = H.emp ∨ ∃ m, m ∈ H.om ∧ H.IsSuc n m) (by hdef) (Or.inl rfl)
    (fun n hn _ => Or.inr ⟨n, hn, H.isSuc_iff.mpr rfl⟩) n h |>.imp id
    fun ⟨m, hm, hs⟩ => ⟨m, hm, H.isSuc_iff.mp hs⟩

/-- Members of natural numbers are natural numbers and are subsets. -/
theorem om_trans : ∀ n, n ∈ H.om → ∀ m, m ∈ n → m ∈ H.om ∧ H.Sub m n :=
  H.om_ind (fun n => ∀ m, m ∈ n → m ∈ H.om ∧ ∀ z, z ∈ m → z ∈ n) (by hdef)
    (fun m hm => (H.not_mem_emp m hm).elim)
    (fun n hn ih m hm => by
      rcases H.mem_suc.mp hm with h | h
      · exact ⟨(ih m h).1, fun z hz => H.mem_suc.mpr (Or.inl ((ih m h).2 z hz))⟩
      · rw [h]
        exact ⟨hn, fun z hz => H.mem_suc.mpr (Or.inl hz)⟩)

theorem mem_om_of_mem {n m : H.W} (hn : n ∈ H.om) (hm : m ∈ n) : m ∈ H.om :=
  (H.om_trans n hn m hm).1

theorem om_mem_trans {n m k : H.W} (hn : n ∈ H.om) (hm : m ∈ n) (hk : k ∈ m) : k ∈ n :=
  (H.om_trans n hn m hm).2 k hk

theorem emp_mem_or {n : H.W} (h : n ∈ H.om) : n = H.emp ∨ H.emp ∈ n :=
  H.om_ind (fun n => (∀ z, ¬ z ∈ n) ∨ ∃ e, e ∈ n ∧ ∀ z, ¬ z ∈ e) (by hdef)
    (Or.inl H.not_mem_emp)
    (fun n _ ih => Or.inr (by
      rcases ih with h | ⟨e, he, he0⟩
      · exact ⟨n, H.mem_suc.mpr (Or.inr rfl), h⟩
      · exact ⟨e, H.mem_suc.mpr (Or.inl he), he0⟩)) n h |>.imp H.eq_emp
    fun ⟨e, he, he0⟩ => by rw [← H.eq_emp he0]; exact he

/-- If `m < n` then `m + 1 ≤ n`. -/
theorem suc_mem_or : ∀ n, n ∈ H.om → ∀ m, m ∈ n → H.suc m ∈ n ∨ H.suc m = n := by
  have key := H.om_ind (fun n => ∀ m, m ∈ n → ∃ s, H.IsSuc s m ∧ (s ∈ n ∨ s = n)) (by hdef)
    (fun m hm => (H.not_mem_emp m hm).elim)
    (fun n _ ih m hm => by
      refine ⟨H.suc m, H.isSuc_iff.mpr rfl, ?_⟩
      rcases H.mem_suc.mp hm with h | h
      · obtain ⟨s, hs, h'⟩ := ih m h
        rw [H.isSuc_iff.mp hs] at h'
        rcases h' with h' | h'
        · exact Or.inl (H.mem_suc.mpr (Or.inl h'))
        · exact Or.inl (H.mem_suc.mpr (Or.inr h'))
      · exact Or.inr (by rw [h]))
  intro n hn m hm
  obtain ⟨s, hs, h'⟩ := key n hn m hm
  rw [H.isSuc_iff.mp hs] at h'
  exact h'

/-- The natural numbers are linearly ordered by membership. -/
theorem om_tri : ∀ m, m ∈ H.om → ∀ n, n ∈ H.om → m ∈ n ∨ m = n ∨ n ∈ m := by
  have key := H.om_ind (fun m => ∀ n, n ∈ H.om → m ∈ n ∨ m = n ∨ n ∈ m) (by hdef)
    (fun n hn => by
      rcases H.emp_mem_or hn with h | h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h)
    (fun m _ ih n hn => by
      rcases ih n hn with h | h | h
      · rcases H.suc_mem_or n hn m h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (H.mem_suc.mpr (Or.inr h.symm)))
      · exact Or.inr (Or.inr (H.mem_suc.mpr (Or.inl h))))
  exact key

theorem om_lt_iff {m n : H.W} (hm : m ∈ H.om) (hn : n ∈ H.om) : H.lt m n ↔ m ∈ n := by
  refine ⟨fun h => ?_, H.mem_lt m n⟩
  rcases H.om_tri m hm n hn with h' | h' | h'
  · exact h'
  · exact (H.lt_ne h h').elim
  · exact (H.lt_asymm h (H.mem_lt n m h')).elim

theorem suc_inj {m n : H.W} (h : H.suc m = H.suc n) : m = n := by
  have h1 : m ∈ H.suc n := by rw [← h]; exact H.mem_suc.mpr (Or.inr rfl)
  have h2 : n ∈ H.suc m := by rw [h]; exact H.mem_suc.mpr (Or.inr rfl)
  rcases H.mem_suc.mp h1 with e | e
  · rcases H.mem_suc.mp h2 with e' | e'
    · exact (H.mem_asymm e e').elim
    · exact e'.symm
  · exact e

theorem suc_ne_emp (n : H.W) : H.suc n ≠ H.emp :=
  fun h => H.not_mem_emp n (h ▸ H.mem_suc.mpr (Or.inr rfl))

/-- The numbers `1` and `2`. -/
noncomputable def one : H.W := H.suc H.emp

noncomputable def two : H.W := H.suc H.one

theorem one_mem_om : H.one ∈ H.om := H.suc_mem_om H.emp_mem_om

theorem two_mem_om : H.two ∈ H.om := H.suc_mem_om H.one_mem_om

theorem one_ne_emp : H.one ≠ H.emp := H.suc_ne_emp _

end Host


/-! ## Finite sets and closed levels -/

namespace Host

variable (H : Host)

theorem mem_one {z : H.W} : z ∈ H.one ↔ z = H.emp := by
  show z ∈ H.suc H.emp ↔ _
  rw [mem_suc]
  exact ⟨fun h => h.elim (fun h => (H.not_mem_emp z h).elim) id, Or.inr⟩

theorem mem_two {z : H.W} : z ∈ H.two ↔ z = H.emp ∨ z = H.one := by
  show z ∈ H.suc H.one ↔ _
  rw [mem_suc, mem_one]

theorem not_mem_self_om {n : H.W} : ¬ n ∈ n := H.mem_irrefl n

/-- The function `f` with one more pair. -/
noncomputable def ins (f a b : H.W) : H.W := H.bun f (H.sg (H.op a b))

theorem app_ins {f a b u v : H.W} : H.App (H.ins f a b) u v ↔ H.App f u v ∨ (u = a ∧ v = b) := by
  rw [app_iff, app_iff]
  show H.op u v ∈ H.bun f (H.sg (H.op a b)) ↔ _
  rw [mem_bun, mem_sg]
  exact or_congr Iff.rfl ⟨fun h => H.op_inj h, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩

theorem isFun_ins {f a b : H.W} (hf : H.IsFun f) (ha : ¬ ∃ v, H.App f a v) :
    H.IsFun (H.ins f a b) := by
  constructor
  · intro p hp
    rcases H.mem_bun.mp hp with h | h
    · exact hf.1 p h
    · exact ⟨a, b, H.isOp_iff.mpr (H.mem_sg.mp h)⟩
  · intro u v v' h h'
    rcases H.app_ins.mp h with h | ⟨h1, h2⟩
    · rcases H.app_ins.mp h' with h' | ⟨h1', -⟩
      · exact hf.2 u v v' h h'
      · exact (ha ⟨v, h1' ▸ h⟩).elim
    · rcases H.app_ins.mp h' with h' | ⟨-, h2'⟩
      · exact (ha ⟨v', h1 ▸ h'⟩).elim
      · rw [h2, h2']

theorem funOn_ins {f n b : H.W} (hf : H.FunOn f n) : H.FunOn (H.ins f n b) (H.suc n) := by
  have hn : ¬ ∃ v, H.App f n v := fun ⟨v, hv⟩ => H.mem_irrefl n ((hf.2 n).mpr ⟨v, hv⟩)
  refine ⟨H.isFun_ins hf.1 hn, fun a => ?_⟩
  rw [mem_suc, hf.2 a]
  constructor
  · rintro (⟨v, hv⟩ | h)
    · exact ⟨v, H.app_ins.mpr (Or.inl hv)⟩
    · exact ⟨b, H.app_ins.mpr (Or.inr ⟨h, rfl⟩)⟩
  · rintro ⟨v, hv⟩
    rcases H.app_ins.mp hv with h | ⟨h, -⟩
    · exact Or.inl ⟨v, h⟩
    · exact Or.inr h

theorem isFun_emp : H.IsFun H.emp :=
  ⟨fun p hp => (H.not_mem_emp p hp).elim, fun _ _ _ h => (H.not_mem_emp _ (H.app_iff.mp h)).elim⟩

theorem funOn_emp : H.FunOn H.emp H.emp :=
  ⟨H.isFun_emp, fun a => ⟨fun h => (H.not_mem_emp a h).elim,
    fun ⟨_, h⟩ => (H.not_mem_emp _ (H.app_iff.mp h)).elim⟩⟩

/-- The restriction of a set of pairs to the arguments in `d`. -/
noncomputable def res (f d : H.W) : H.W :=
  H.sepS f (fun p => ∃ a b, a ∈ d ∧ p = H.op a b) (by hdef)

theorem app_res {f d a b : H.W} : H.App (H.res f d) a b ↔ a ∈ d ∧ H.App f a b := by
  rw [app_iff, app_iff]
  show H.op a b ∈ H.sepS _ _ _ ↔ _
  rw [mem_sepS]
  constructor
  · rintro ⟨h, a', b', ha', e⟩
    obtain ⟨e1, -⟩ := H.op_inj e
    exact ⟨e1 ▸ ha', h⟩
  · rintro ⟨ha, h⟩
    exact ⟨h, a, b, ha, rfl⟩

theorem isFun_res {f d : H.W} (hf : H.IsFun f) : H.IsFun (H.res f d) :=
  ⟨fun p hp => hf.1 p (H.mem_sepS.mp hp).1,
    fun a b b' h h' => hf.2 a b b' (H.app_res.mp h).2 (H.app_res.mp h').2⟩

theorem funOn_res {f n d : H.W} (hf : H.FunOn f n) (hd : H.Sub d n) : H.FunOn (H.res f d) d :=
  ⟨H.isFun_res hf.1, fun a => ⟨fun ha => by
      obtain ⟨b, hb⟩ := (hf.2 a).mp (hd a ha)
      exact ⟨b, H.app_res.mpr ⟨ha, hb⟩⟩,
    fun ⟨_, hb⟩ => (H.app_res.mp hb).1⟩⟩

/-- `x` is finite: it is the set of the values of a function on a natural number. -/
def Fin (x : H.W) : Prop :=
  ∃ n f, n ∈ H.om ∧ H.FunOn f n ∧ ∀ z, z ∈ x ↔ ∃ i, H.App f i z

theorem fin_emp : H.Fin H.emp :=
  ⟨H.emp, H.emp, H.emp_mem_om, H.funOn_emp, fun z => ⟨fun h => (H.not_mem_emp z h).elim,
    fun ⟨_, h⟩ => (H.not_mem_emp _ (H.app_iff.mp h)).elim⟩⟩

theorem fin_ins {x : H.W} (hx : H.Fin x) (a : H.W) : H.Fin (H.bun x (H.sg a)) := by
  obtain ⟨n, f, hn, hf, hx⟩ := hx
  refine ⟨H.suc n, H.ins f n a, H.suc_mem_om hn, H.funOn_ins hf, fun z => ?_⟩
  rw [mem_bun, mem_sg, hx z]
  constructor
  · rintro (⟨i, hi⟩ | h)
    · exact ⟨i, H.app_ins.mpr (Or.inl hi)⟩
    · exact ⟨n, H.app_ins.mpr (Or.inr ⟨rfl, h⟩)⟩
  · rintro ⟨i, hi⟩
    rcases H.app_ins.mp hi with h | ⟨-, h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr h

/-- Induction on finite sets for a definable predicate. -/
theorem fin_ind (P : H.W → Prop) (hP : Def1 H P) (h0 : P H.emp)
    (hs : ∀ x a, H.Fin x → P x → P (H.bun x (H.sg a))) : ∀ x, H.Fin x → P x := by
  have key := H.om_ind
    (fun n => ∀ f x, H.FunOn f n → (∀ z, z ∈ x ↔ ∃ i, H.App f i z) → P x) (by hdef)
    (fun f x hf hx => by
      have : x = H.emp := H.eq_emp fun z hz => by
        obtain ⟨i, hi⟩ := (hx z).mp hz
        exact H.not_mem_emp i ((hf.2 i).mpr ⟨z, hi⟩)
      rw [this]
      exact h0)
    (fun n hn ih f x hf hx => by
      obtain ⟨a, ha⟩ := (hf.2 n).mp (H.mem_suc.mpr (Or.inr rfl))
      have hsub : H.Sub n (H.suc n) := fun z hz => H.mem_suc.mpr (Or.inl hz)
      obtain ⟨x', hx'⟩ := H.sep' x (fun z => ∃ i, H.App (H.res f n) i z) (by hdef)
      have hx'' : ∀ z, z ∈ x' ↔ ∃ i, H.App (H.res f n) i z := fun z =>
        (hx' z).trans ⟨fun h => h.2, fun ⟨i, hi⟩ => ⟨(hx z).mpr ⟨i, (H.app_res.mp hi).2⟩, i, hi⟩⟩
      have hfin : H.Fin x' := ⟨n, H.res f n, hn, H.funOn_res hf hsub, hx''⟩
      have hP' := ih (H.res f n) x' (H.funOn_res hf hsub) hx''
      have e : x = H.bun x' (H.sg a) := H.ext' fun z => by
        rw [mem_bun, mem_sg, hx z, hx'' z]
        constructor
        · rintro ⟨i, hi⟩
          rcases H.mem_suc.mp ((hf.2 i).mpr ⟨z, hi⟩) with h | h
          · exact Or.inl ⟨i, H.app_res.mpr ⟨h, hi⟩⟩
          · exact Or.inr (hf.1.2 n z a (h ▸ hi) ha)
        · rintro (⟨i, hi⟩ | h)
          · exact ⟨i, (H.app_res.mp hi).2⟩
          · exact ⟨n, h ▸ ha⟩
      rw [e]
      exact hs x' a hfin hP')
  rintro x ⟨n, f, hn, hf, hx⟩
  exact key n hn f x hf hx

theorem fin_sg (a : H.W) : H.Fin (H.sg a) := by
  have h := H.fin_ins H.fin_emp a
  have e : H.bun H.emp (H.sg a) = H.sg a := H.ext' fun z => by
    rw [mem_bun]
    exact ⟨fun h => h.elim (fun h => (H.not_mem_emp z h).elim) id, Or.inr⟩
  rwa [e] at h

theorem fin_up (a b : H.W) : H.Fin (H.up a b) := by
  have h := H.fin_ins (H.fin_sg a) b
  have e : H.bun (H.sg a) (H.sg b) = H.up a b := H.ext' fun z => by
    rw [mem_bun, mem_sg, mem_sg, mem_up]
  rwa [e] at h

/-- A subset of a finite set is finite. -/
theorem fin_sub {x : H.W} (hx : H.Fin x) : ∀ y, H.Sub y x → H.Fin y := by
  refine H.fin_ind (fun x => ∀ y, (∀ z, z ∈ y → z ∈ x) → H.Fin y) (by hdef) ?_ ?_ x hx
  · intro y hy
    rw [H.eq_emp fun z hz => H.not_mem_emp z (hy z hz)]
    exact H.fin_emp
  · intro x a _ ih y hy
    obtain ⟨y', hy'⟩ := H.sep' y (fun z => z ≠ a) (by hdef)
    have h1 : H.Fin y' := ih y' fun z hz => by
      rcases H.mem_bun.mp (hy z ((hy' z).mp hz).1) with h | h
      · exact h
      · exact (((hy' z).mp hz).2 (H.mem_sg.mp h)).elim
    by_cases ha : a ∈ y
    · have e : y = H.bun y' (H.sg a) := H.ext' fun z => by
        rw [mem_bun, mem_sg, hy' z]
        constructor
        · intro hz
          by_cases hza : z = a
          · exact Or.inr hza
          · exact Or.inl ⟨hz, hza⟩
        · rintro (h | h)
          · exact h.1
          · rw [h]; exact ha
      rw [e]
      exact H.fin_ins h1 a
    · have e : y = y' := H.ext' fun z => by
        rw [hy' z]
        exact ⟨fun hz => ⟨hz, fun e => ha (e ▸ hz)⟩, fun h => h.1⟩
      rw [e]
      exact h1

/-- The union of two finite sets is finite. -/
theorem fin_bun {x y : H.W} (hx : H.Fin x) (hy : H.Fin y) : H.Fin (H.bun x y) := by
  refine H.fin_ind (fun y => H.Fin (H.bun x y)) (by hdef) ?_ ?_ y hy
  · have e : H.bun x H.emp = x := H.ext' fun z => by
      rw [mem_bun]
      exact ⟨fun h => h.elim id (fun h => (H.not_mem_emp z h).elim), Or.inl⟩
    show H.Fin (H.bun x H.emp)
    rw [e]
    exact hx
  · intro y a _ ih
    have e : H.bun x (H.bun y (H.sg a)) = H.bun (H.bun x y) (H.sg a) := H.ext' fun z => by
      simp only [mem_bun]
      exact (or_assoc).symm
    show H.Fin (H.bun x (H.bun y (H.sg a)))
    rw [e]
    exact H.fin_ins ih a

/-- A nonempty finite set has a greatest element for the global order. -/
theorem fin_max {x : H.W} (hx : H.Fin x) : x ≠ H.emp →
    ∃ m, m ∈ x ∧ ∀ z, z ∈ x → z = m ∨ H.lt z m := by
  refine H.fin_ind (fun x => x ≠ H.emp → ∃ m, m ∈ x ∧ ∀ z, z ∈ x → z = m ∨ H.lt z m) (by hdef)
    (fun h => (h rfl).elim) ?_ x hx
  intro x a _ ih _
  by_cases hx0 : x = H.emp
  · refine ⟨a, H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl)), fun z hz => ?_⟩
    rcases H.mem_bun.mp hz with h | h
    · rw [hx0] at h
      exact (H.not_mem_emp z h).elim
    · exact Or.inl (H.mem_sg.mp h)
  · obtain ⟨m, hm, hmax⟩ := ih hx0
    rcases H.lt_tri a m with h | h | h
    · refine ⟨m, H.mem_bun.mpr (Or.inl hm), fun z hz => ?_⟩
      rcases H.mem_bun.mp hz with h' | h'
      · exact hmax z h'
      · rw [H.mem_sg.mp h']
        exact Or.inr h
    · refine ⟨m, H.mem_bun.mpr (Or.inl hm), fun z hz => ?_⟩
      rcases H.mem_bun.mp hz with h' | h'
      · exact hmax z h'
      · rw [H.mem_sg.mp h', h]
        exact Or.inl rfl
    · refine ⟨a, H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl)), fun z hz => ?_⟩
      rcases H.mem_bun.mp hz with h' | h'
      · rcases hmax z h' with e | e
        · rw [e]
          exact Or.inr h
        · exact Or.inr (H.lt_trans _ _ _ e h)
      · exact Or.inl (H.mem_sg.mp h')

/-! ### Closed levels -/

/-- A closed level: a transitive set that contains the subsets of its elements, bounds the
values of every function whose domain is one of its elements, and contains the initial segments
of the global order below its elements. -/
structure Closed (M : H.W) : Prop where
  trans : ∀ x y, x ∈ y → y ∈ M → x ∈ M
  sub : ∀ x y, H.Sub x y → y ∈ M → x ∈ M
  bd : ∀ f, H.IsFun f → H.dom f ∈ M → (∀ a b, H.App f a b → b ∈ M) →
    ∃ y, y ∈ M ∧ ∀ a b, H.App f a b → b ∈ y
  seg : ∀ a, a ∈ M → ∃ s, s ∈ M ∧ ∀ y, y ∈ s ↔ y ∈ M ∧ H.lt y a
  om_mem : H.om ∈ M

variable {H}

namespace Closed

variable {M : H.W} (hM : H.Closed M)
include hM

theorem emp_mem : H.emp ∈ M :=
  hM.sub _ _ (fun z hz => (H.not_mem_emp z hz).elim) hM.om_mem

theorem nat_mem {n : H.W} (hn : n ∈ H.om) : n ∈ M := hM.trans n _ hn hM.om_mem

/-- The range of a function with domain in `M` and values in `M` is an element of `M`. -/
theorem ran_mem {f : H.W} (hf : H.IsFun f) (hd : H.dom f ∈ M) (hv : ∀ a b, H.App f a b → b ∈ M) :
    H.ran f ∈ M := by
  obtain ⟨y, hy, hb⟩ := hM.bd f hf hd hv
  exact hM.sub _ y (fun b hb' => by
    obtain ⟨a, ha⟩ := H.mem_ran.mp hb'
    exact hb a b ha) hy

theorem up_mem {a b : H.W} (ha : a ∈ M) (hb : b ∈ M) : H.up a b ∈ M := by
  have hf : H.FunOn (H.ins (H.ins H.emp H.emp a) H.one b) H.two :=
    H.funOn_ins (H.funOn_ins H.funOn_emp)
  have hd : H.dom (H.ins (H.ins H.emp H.emp a) H.one b) = H.two :=
    H.domIs_unique (H.domIs_dom _) hf.2
  obtain ⟨y, hy, hb'⟩ := hM.bd _ hf.1 (by rw [hd]; exact hM.nat_mem H.two_mem_om) (fun u v h => by
    rcases H.app_ins.mp h with h | ⟨-, h⟩
    · rcases H.app_ins.mp h with h | ⟨-, h⟩
      · exact (H.not_mem_emp _ (H.app_iff.mp h)).elim
      · rw [h]; exact ha
    · rw [h]; exact hb)
  refine hM.sub _ y (fun z hz => ?_) hy
  rcases H.mem_up.mp hz with h | h
  · rw [h]
    exact hb' H.emp a (H.app_ins.mpr (Or.inl (H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩))))
  · rw [h]
    exact hb' H.one b (H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩))

theorem sg_mem {a : H.W} (ha : a ∈ M) : H.sg a ∈ M := hM.up_mem ha ha

theorem op_mem {a b : H.W} (ha : a ∈ M) (hb : b ∈ M) : H.op a b ∈ M :=
  hM.up_mem (hM.sg_mem ha) (hM.up_mem ha hb)

theorem of_op_mem {a b : H.W} (h : H.op a b ∈ M) : a ∈ M ∧ b ∈ M :=
  ⟨hM.trans _ _ (H.mem_sg.mpr rfl) (hM.trans _ _ (H.mem_up.mpr (Or.inl rfl)) h),
    hM.trans _ _ (H.mem_up.mpr (Or.inr rfl)) (hM.trans _ _ (H.mem_up.mpr (Or.inr rfl)) h)⟩

theorem un_mem {x : H.W} (hx : x ∈ M) : H.un x ∈ M := by
  obtain ⟨s, hs, hsm⟩ := hM.seg x hx
  refine hM.sub _ s (fun z hz => ?_) hs
  obtain ⟨y, hy, hzy⟩ := H.mem_un.mp hz
  exact (hsm z).mpr ⟨hM.trans z y hzy (hM.trans y x hy hx),
    H.lt_trans _ _ _ (H.mem_lt _ _ hzy) (H.mem_lt _ _ hy)⟩

theorem bun_mem {a b : H.W} (ha : a ∈ M) (hb : b ∈ M) : H.bun a b ∈ M :=
  hM.un_mem (hM.up_mem ha hb)

theorem suc_mem {a : H.W} (ha : a ∈ M) : H.suc a ∈ M := hM.bun_mem ha (hM.sg_mem ha)

/-- A finite set of elements of `M` is an element of `M`. -/
theorem fin_mem {x : H.W} (hx : H.Fin x) : H.Sub x M → x ∈ M := by
  refine H.fin_ind (fun x => (∀ z, z ∈ x → z ∈ M) → x ∈ M) (by hdef) (fun _ => hM.emp_mem) ?_ x hx
  intro x a _ ih h
  exact hM.bun_mem (ih fun z hz => h z (H.mem_bun.mpr (Or.inl hz)))
    (hM.sg_mem (h a (H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl)))))

theorem sepS_mem {a : H.W} (ha : a ∈ M) (P : H.W → Prop) (hP : Def1 H P) : H.sepS a P hP ∈ M :=
  hM.sub _ a (fun _ hz => (H.mem_sepS.mp hz).1) ha

/-- The product of two elements of `M` is an element of `M`. -/
theorem prod_mem {a b : H.W} (ha : a ∈ M) (hb : b ∈ M) : H.prod a b ∈ M := by
  have h1 : ∀ u, u ∈ a → ∃ s, s ∈ M ∧ ∀ p, p ∈ s ↔ ∃ v, v ∈ b ∧ p = H.op u v := by
    intro u hu
    have hfun : ∀ v, v ∈ b → ∀ p p', p = H.op u v → p' = H.op u v → p = p' :=
      fun _ _ _ _ e e' => e.trans e'.symm
    have hd : H.dom (H.mkFun b (fun v p => p = H.op u v) (by hdef) hfun) = b :=
      H.ext' fun v => H.mem_dom.trans
        ⟨fun ⟨_, h⟩ => (H.app_mkFun.mp h).1, fun h => ⟨_, H.app_mkFun.mpr ⟨h, rfl⟩⟩⟩
    obtain ⟨y, hy, hb'⟩ := hM.bd _ H.isFun_mkFun (by rw [hd]; exact hb) (fun v p h => by
      obtain ⟨hv, e⟩ := H.app_mkFun.mp h
      rw [e]
      exact hM.op_mem (hM.trans u a hu ha) (hM.trans v b hv hb))
    refine ⟨H.sepS y (fun p => ∃ v, v ∈ b ∧ p = H.op u v) (by hdef), hM.sepS_mem hy _ _, fun p => ?_⟩
    rw [H.mem_sepS]
    exact ⟨fun h => h.2, fun ⟨v, hv, e⟩ => ⟨hb' v p (H.app_mkFun.mpr ⟨hv, e⟩), v, hv, e⟩⟩
  have hfun : ∀ u, u ∈ a → ∀ s s', (∀ p, p ∈ s ↔ ∃ v, v ∈ b ∧ p = H.op u v) →
      (∀ p, p ∈ s' ↔ ∃ v, v ∈ b ∧ p = H.op u v) → s = s' :=
    fun u _ s s' hs hs' => H.ext' fun p => (hs p).trans (hs' p).symm
  have hd : H.dom (H.mkFun a (fun u s => ∀ p, p ∈ s ↔ ∃ v, v ∈ b ∧ p = H.op u v) (by hdef) hfun)
      = a :=
    H.ext' fun u => H.mem_dom.trans ⟨fun ⟨_, h⟩ => (H.app_mkFun.mp h).1, fun h => by
      obtain ⟨s, -, hs⟩ := h1 u h
      exact ⟨s, H.app_mkFun.mpr ⟨h, hs⟩⟩⟩
  obtain ⟨Y, hY, hb'⟩ := hM.bd _ H.isFun_mkFun (by rw [hd]; exact ha) (fun u s h => by
    obtain ⟨hu, hs⟩ := H.app_mkFun.mp h
    obtain ⟨s', hs'M, hs'⟩ := h1 u hu
    rw [hfun u hu s s' hs hs']
    exact hs'M)
  refine hM.sub _ (H.un Y) (fun p hp => ?_) (hM.un_mem hY)
  obtain ⟨u, v, hu, hv, e⟩ := H.mem_prod.mp hp
  obtain ⟨s, -, hs⟩ := h1 u hu
  exact H.mem_un.mpr ⟨s, hb' u s (H.app_mkFun.mpr ⟨hu, hs⟩), (hs p).mpr ⟨v, hv, e⟩⟩

/-- A function with domain in `M` and values in `M` is an element of `M`. -/
theorem fun_mem {f n : H.W} (hf : H.FunOn f n) (hn : n ∈ M) (hv : ∀ a b, H.App f a b → b ∈ M) :
    f ∈ M := by
  have hd : H.dom f = n := H.domIs_unique (H.domIs_dom f) hf.2
  obtain ⟨y, hy, hb⟩ := hM.bd f hf.1 (by rw [hd]; exact hn) hv
  refine hM.sub _ (H.prod n y) (fun p hp => ?_) (hM.prod_mem hn hy)
  obtain ⟨a, b, hab⟩ := hf.1.1 p hp
  rw [H.isOp_iff.mp hab] at hp ⊢
  exact H.op_mem_prod.mpr ⟨(hf.2 a).mpr ⟨b, H.app_iff.mpr hp⟩, hb a b (H.app_iff.mpr hp)⟩

end Closed

end Host


/-! ## The pool: atoms, labels and incidence -/

namespace Host

variable (H : Host)

/-- The atom with prescribed set `X` of adjacent earlier labels and index `η`. -/
noncomputable def atom (X η : H.W) : H.W := H.op H.emp (H.op X η)

/-- The label with reservoir `r`, slot `ξ`, prescribed set `X` of adjacent earlier atoms and
index `η`. -/
noncomputable def label (r ξ X η : H.W) : H.W := H.op H.one (H.op r (H.op ξ (H.op X η)))

theorem atom_inj {X η X' η' : H.W} (h : H.atom X η = H.atom X' η') : X = X' ∧ η = η' :=
  H.op_inj (H.op_inj h).2

theorem label_inj {r ξ X η r' ξ' X' η' : H.W} (h : H.label r ξ X η = H.label r' ξ' X' η') :
    r = r' ∧ ξ = ξ' ∧ X = X' ∧ η = η' := by
  obtain ⟨h1, h2⟩ := H.op_inj (H.op_inj h).2
  obtain ⟨h3, h4⟩ := H.op_inj h2
  obtain ⟨h5, h6⟩ := H.op_inj h4
  exact ⟨h1, h3, h5, h6⟩

theorem atom_ne_label {X η r ξ X' η' : H.W} : H.atom X η ≠ H.label r ξ X' η' :=
  fun h => H.one_ne_emp (H.op_inj h).1.symm

/-- `a` is an atom of the pool on the level `M`. -/
def IsAtom (M a : H.W) : Prop := a ∈ M ∧ ∃ X η, a = H.atom X η

/-- `b` is a label of the pool on the level `M`. -/
def IsLabel (M b : H.W) : Prop := b ∈ M ∧ ∃ r ξ X η, b = H.label r ξ X η

/-- Incidence between an atom and a label: one of them lists the other. -/
def Adj (a b : H.W) : Prop :=
  (∃ X η, a = H.atom X η ∧ b ∈ X) ∨ (∃ r ξ X η, b = H.label r ξ X η ∧ a ∈ X)

theorem lt_atom_X (X η : H.W) : H.lt X (H.atom X η) :=
  H.lt_trans _ _ _ (H.lt_op_left X η) (H.lt_op_right _ _)

theorem lt_atom_eta (X η : H.W) : H.lt η (H.atom X η) :=
  H.lt_trans _ _ _ (H.lt_op_right X η) (H.lt_op_right _ _)

theorem lt_label_r (r ξ X η : H.W) : H.lt r (H.label r ξ X η) :=
  H.lt_trans _ _ _ (H.lt_op_left r _) (H.lt_op_right _ _)

theorem lt_label_xi (r ξ X η : H.W) : H.lt ξ (H.label r ξ X η) :=
  H.lt_trans _ _ _ (H.lt_op_left ξ _) (H.lt_trans _ _ _ (H.lt_op_right r _) (H.lt_op_right _ _))

theorem lt_label_X (r ξ X η : H.W) : H.lt X (H.label r ξ X η) :=
  H.lt_trans _ _ _ (H.lt_op_left X η)
    (H.lt_trans _ _ _ (H.lt_op_right ξ _) (H.lt_trans _ _ _ (H.lt_op_right r _) (H.lt_op_right _ _)))

theorem lt_label_eta (r ξ X η : H.W) : H.lt η (H.label r ξ X η) :=
  H.lt_trans _ _ _ (H.lt_op_right X η)
    (H.lt_trans _ _ _ (H.lt_op_right ξ _) (H.lt_trans _ _ _ (H.lt_op_right r _) (H.lt_op_right _ _)))

/-- An atom that a label lists precedes the label. -/
theorem adj_lt_of_label {a r ξ X η : H.W} (h : a ∈ X) : H.lt a (H.label r ξ X η) :=
  H.lt_trans _ _ _ (H.mem_lt _ _ h) (H.lt_label_X r ξ X η)

/-- A label that an atom lists precedes the atom. -/
theorem adj_lt_of_atom {b X η : H.W} (h : b ∈ X) : H.lt b (H.atom X η) :=
  H.lt_trans _ _ _ (H.mem_lt _ _ h) (H.lt_atom_X X η)

variable {H}

theorem Closed.atom_mem {M X η : H.W} (hM : H.Closed M) (hX : X ∈ M) (hη : η ∈ M) :
    H.atom X η ∈ M :=
  hM.op_mem hM.emp_mem (hM.op_mem hX hη)

theorem Closed.label_mem {M r ξ X η : H.W} (hM : H.Closed M) (hr : r ∈ M) (hξ : ξ ∈ M)
    (hX : X ∈ M) (hη : η ∈ M) : H.label r ξ X η ∈ M :=
  hM.op_mem (hM.nat_mem H.one_mem_om) (hM.op_mem hr (hM.op_mem hξ (hM.op_mem hX hη)))

/-- **Genericity for atoms.** For sets `P`, `N`, `Z` in the level with `P` and `N` disjoint
there is an atom adjacent to every label in `P`, to no label in `N`, and not in `Z`. -/
theorem Closed.exists_atom {M P N Z : H.W} (hM : H.Closed M) (hP : P ∈ M) (hN : N ∈ M)
    (hZ : Z ∈ M) (hdisj : ∀ b, b ∈ P → ¬ b ∈ N) :
    ∃ a, H.IsAtom M a ∧ (∀ b, b ∈ P → H.Adj a b) ∧ (∀ b, b ∈ N → ¬ H.Adj a b) ∧ ¬ a ∈ Z := by
  refine ⟨H.atom P (H.op N Z), ⟨hM.atom_mem hP (hM.op_mem hN hZ), P, _, rfl⟩,
    fun b hb => Or.inl ⟨P, _, rfl, hb⟩, fun b hb => ?_, fun h => ?_⟩
  · rintro (⟨X, η, e, hbX⟩ | ⟨r, ξ, X, η, e, haX⟩)
    · rw [← (H.atom_inj e).1] at hbX
      exact hdisj b hbX hb
    · have h1 : H.lt (H.atom P (H.op N Z)) b := e ▸ H.adj_lt_of_label haX
      have h2 : H.lt b (H.atom P (H.op N Z)) :=
        H.lt_trans _ _ _ (H.mem_lt _ _ hb)
          (H.lt_trans _ _ _ (H.lt_op_left N Z) (H.lt_atom_eta P _))
      exact H.lt_asymm h1 h2
  · exact H.lt_asymm (H.mem_lt _ _ h)
      (H.lt_trans _ _ _ (H.lt_op_right N Z) (H.lt_atom_eta P _))

/-- **Genericity for labels.** For any reservoir and slot, and sets `P`, `N`, `Z` in the level
with `P` and `N` disjoint, there is a label with that reservoir and slot adjacent to every atom
in `P`, to no atom in `N`, and not in `Z`. -/
theorem Closed.exists_label {M r ξ P N Z : H.W} (hM : H.Closed M) (hr : r ∈ M) (hξ : ξ ∈ M)
    (hP : P ∈ M) (hN : N ∈ M) (hZ : Z ∈ M) (hdisj : ∀ a, a ∈ P → ¬ a ∈ N) :
    ∃ b, b = H.label r ξ P (H.op N Z) ∧ b ∈ M ∧ (∀ a, a ∈ P → H.Adj a b) ∧
      (∀ a, a ∈ N → ¬ H.Adj a b) ∧ ¬ b ∈ Z := by
  refine ⟨_, rfl, hM.label_mem hr hξ hP (hM.op_mem hN hZ),
    fun a ha => Or.inr ⟨r, ξ, P, _, rfl, ha⟩, fun a ha => ?_, fun h => ?_⟩
  · rintro (⟨X, η, e, hbX⟩ | ⟨r', ξ', X, η, e, haX⟩)
    · have h1 : H.lt (H.label r ξ P (H.op N Z)) a := e ▸ H.adj_lt_of_atom hbX
      have h2 : H.lt a (H.label r ξ P (H.op N Z)) :=
        H.lt_trans _ _ _ (H.mem_lt _ _ ha)
          (H.lt_trans _ _ _ (H.lt_op_left N Z) (H.lt_label_eta r ξ P _))
      exact H.lt_asymm h1 h2
    · rw [← (H.label_inj e).2.2.1] at haX
      exact hdisj a haX ha
  · exact H.lt_asymm (H.mem_lt _ _ h)
      (H.lt_trans _ _ _ (H.lt_op_right N Z) (H.lt_label_eta r ξ P _))

/-- The set of atoms of the pool. -/
noncomputable def atoms (H : Host) (M : H.W) : H.W := H.sepS M (fun a => ∃ X η, a = H.atom X η) (by hdef)

theorem mem_atoms {M a : H.W} : a ∈ H.atoms M ↔ H.IsAtom M a := H.mem_sepS

/-- The set of labels of the pool. -/
noncomputable def labels (H : Host) (M : H.W) : H.W :=
  H.sepS M (fun b => ∃ r ξ X η, b = H.label r ξ X η) (by hdef)

theorem mem_labels {M b : H.W} : b ∈ H.labels M ↔ H.IsLabel M b := H.mem_sepS

/-- Two labels with the same adjacent atoms are equal. -/
theorem Closed.label_ext {M b b' : H.W} (hM : H.Closed M) (hb : b ∈ M) (hb' : b' ∈ M)
    (h : ∀ a, H.IsAtom M a → (H.Adj a b ↔ H.Adj a b')) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, h1, h2, -⟩ := hM.exists_atom (hM.sg_mem hb) (hM.sg_mem hb') hM.emp_mem
    (fun x hx hx' => hne ((H.mem_sg.mp hx).symm.trans (H.mem_sg.mp hx')))
  exact h2 b' (H.mem_sg.mpr rfl) ((h a ha).mp (h1 b (H.mem_sg.mpr rfl)))

end Host


/-! ## Paths, tokens, and the definition of the stages -/

namespace Host

variable (H : Host)

/-- A path: a set of proper levels (the level `0` of the atoms is implicit). -/
def IsPath (d p : H.W) : Prop := ∀ x, x ∈ p → x ∈ H.suc d ∧ x ≠ H.emp

/-- The type of a path: its greatest element, or `0` for the empty path. -/
def PType (p β : H.W) : Prop := (p = H.emp ∧ β = H.emp) ∨ (β ∈ p ∧ ∀ x, x ∈ p → x ∈ H.suc β)

/-- `δ` is the least element of `p`. -/
def MinIs (p δ : H.W) : Prop := δ ∈ p ∧ ∀ x, x ∈ p → δ ∈ H.suc x

/-- `P` is `p` without `δ`. -/
def Rest (p δ P : H.W) : Prop := ∀ x, x ∈ P ↔ x ∈ p ∧ x ≠ δ

/-- A token at the level `β`: an atom or a label of the pool with a path of type `β`. At the
level `0` only atoms. -/
def IsTok (M d β v : H.W) : Prop :=
  ∃ t p, v = H.op t p ∧ H.IsPath d p ∧ H.PType p β ∧
    (H.IsAtom M t ∨ (H.IsLabel M t ∧ p ≠ H.emp))

/-- A tuple at the level `β`: a finite sequence of tokens. -/
def IsTup (M d β S : H.W) : Prop :=
  ∃ n, n ∈ H.om ∧ H.FunOn S n ∧ ∀ j v, H.App S j v → H.IsTok M d β v

/-- Two tuples with the same length, and the same paths and kinds at each place. -/
def SameSig (S S0 : H.W) : Prop :=
  ∃ n, H.FunOn S n ∧ H.FunOn S0 n ∧ ∀ j t p t0 p0, H.App S j (H.op t p) → H.App S0 j (H.op t0 p0) →
    p = p0 ∧ ((∃ X η, t = H.atom X η) ↔ ∃ X η, t0 = H.atom X η)

/-! ### Access to the records of the lower stages

`F` is a function on proper levels; its value at `β` is the record
`(τ_β, G_β, action, names, decoding)`. Every access is made from a stage `α` and only to the
levels below `α`. -/

def Rec (F β τ G A N D : H.W) : Prop := H.App F β (H.op τ (H.op G (H.op A (H.op N D))))

/-- `z` is an object of the level `β`, seen from the stage `α`. -/
def InT (M F α β z : H.W) : Prop :=
  (β = H.emp ∧ H.IsAtom M z) ∨ (β ≠ H.emp ∧ β ∈ α ∧ ∃ τ G A N D, H.Rec F β τ G A N D ∧ z ∈ τ)

/-- `π` is an allowable permutation of the level `β`, seen from the stage `α`. -/
def InG (F α β π : H.W) : Prop := β ∈ α ∧ ∃ τ G A N D, H.Rec F β τ G A N D ∧ π ∈ G

/-- `π` sends `x` to `y`, at the level `β`, seen from the stage `α`. -/
def InA (F α β π x y : H.W) : Prop :=
  β ∈ α ∧ ∃ τ G A N D, H.Rec F β τ G A N D ∧ H.op π (H.op x y) ∈ A

/-- `c` is the name of a code of the level `β`, seen from the stage `α`. -/
def InN (F α β c : H.W) : Prop := β ∈ α ∧ ∃ τ G A N D, H.Rec F β τ G A N D ∧ c ∈ N

/-- `(c, S)` is a descriptor at the level `γ`. At the level `0` the codes are the projections
`(k, i)` on atom tuples of length `k`. -/
def Desc (M d F α γ c S : H.W) : Prop :=
  (γ = H.emp ∧ ∃ k i, c = H.op k i ∧ k ∈ H.om ∧ i ∈ k ∧ H.FunOn S k ∧
    ∀ j v, H.App S j v → H.IsTok M d H.emp v) ∨
  (γ ≠ H.emp ∧ H.InN F α γ c ∧ H.IsTup M d γ S ∧ ∃ S0 pat, c = H.op S0 pat ∧ H.SameSig S S0)

/-- The descriptor `(c, S)` at the level `β` decodes to `y`. -/
def InD (M d F α β c S y : H.W) : Prop :=
  (β = H.emp ∧ H.Desc M d F α β c S ∧ ∃ k i, c = H.op k i ∧ H.App S i (H.op y H.emp)) ∨
  (β ≠ H.emp ∧ β ∈ α ∧ ∃ τ G A N D, H.Rec F β τ G A N D ∧ H.op c (H.op S y) ∈ D)

/-! ### The structure of the stage `α` -/

/-- The token `v` is coloured `(γ, δ, c)` with coordinates `S` raised by `P`. -/
def Col (M d F α v γ δ c S P : H.W) : Prop :=
  ∃ p X η, v = H.op (H.label (H.op γ δ) (H.op c S) X η) p ∧ H.MinIs p δ ∧ H.Rest p δ P ∧
    P ≠ H.emp ∧ γ ≠ δ ∧ (∀ x, x ∈ P → γ ∈ x) ∧ H.Desc M d F α γ c S

/-- `w'` is the token `w` with `P` added to its path. -/
def RaiseBy (w P w' : H.W) : Prop := ∃ t u, w = H.op t u ∧ w' = H.op t (H.bun u P)

/-- `θ` is a partial isomorphism of the structure of the stage `α` with closed domain: an
injective function between tokens that preserves paths, kinds, incidence on each path, and
colours together with coordinates (which must be in its domain), and reflects colours. -/
def PIso (M d F α θ : H.W) : Prop :=
  H.IsFun θ ∧
  (∀ v w, H.App θ v w → H.IsTok M d α v ∧ H.IsTok M d α w) ∧
  (∀ v v' w, H.App θ v w → H.App θ v' w → v = v') ∧
  (∀ t p t' p', H.App θ (H.op t p) (H.op t' p') →
    p = p' ∧ ((∃ X η, t = H.atom X η) ↔ ∃ X η, t' = H.atom X η)) ∧
  (∀ a b p a' b', H.App θ (H.op a p) (H.op a' p) → H.App θ (H.op b p) (H.op b' p) →
    (∃ X η, a = H.atom X η) → (∃ r ξ X η, b = H.label r ξ X η) → (H.Adj a b ↔ H.Adj a' b')) ∧
  (∀ v w γ δ c S P, H.App θ v w → H.Col M d F α v γ δ c S P →
    ∃ S', H.Col M d F α w γ δ c S' P ∧
      ∀ j t u, H.App S j (H.op t u) →
        ∃ t', H.App S' j (H.op t' u) ∧ H.App θ (H.op t (H.bun u P)) (H.op t' (H.bun u P))) ∧
  (∀ v w γ δ c S' P, H.App θ v w → H.Col M d F α w γ δ c S' P →
    ∃ S, H.Col M d F α v γ δ c S P)

/-- `π` is an automorphism of the structure of the stage `α`. -/
def IsAut (M d F α π : H.W) : Prop :=
  H.PIso M d F α π ∧ (∀ v, H.IsTok M d α v → ∃ w, H.App π v w) ∧
    (∀ w, H.IsTok M d α w → ∃ v, H.App π v w)

/-- `ρ` is the derivative of `π` at the level `β`. -/
def IsDer (π α β ρ : H.W) : Prop :=
  ∀ q, q ∈ ρ ↔ ∃ t u t', q = H.op (H.op t u) (H.op t' u) ∧ H.PType u β ∧
    H.App π (H.op t (H.bun u (H.sg α))) (H.op t' (H.bun u (H.sg α)))

/-- The action of `π` (at the stage `α`) on an object of the lower level `β`. -/
def ActLow (F α π β z z' : H.W) : Prop :=
  (β = H.emp ∧ H.App π (H.op z (H.sg α)) (H.op z' (H.sg α))) ∨
  (β ≠ H.emp ∧ ∃ ρ, H.IsDer π α β ρ ∧ H.InA F α β ρ z z')

/-- The action of `π` on a pre-object of the stage `α`. -/
def ActRaw (F α π x y : H.W) : Prop :=
  ∃ β D D', x = H.op β D ∧ y = H.op β D' ∧ ∀ z', z' ∈ D' ↔ ∃ z, z ∈ D ∧ H.ActLow F α π β z z'

/-- `l` is the literal litter of the label `b`: the pre-object whose distinguished extension is
the set of the atoms adjacent to `b`. -/
def IsLit (M b l : H.W) : Prop :=
  ∃ L, l = H.op H.emp L ∧ ∀ a, a ∈ L ↔ H.IsAtom M a ∧ H.Adj a b

/-- `Y` is the alternate extension at `δ` of the set `X` of objects of the level `β`: the
literal litters of the labels in the fibres of the descriptors that decode into `X`. -/
def IsAlt (M d F α β δ X Y : H.W) : Prop :=
  ∀ l, l ∈ Y ↔ ∃ c S X' η x, H.Desc M d F α β c S ∧ H.InD M d F α β c S x ∧ x ∈ X ∧
    H.label (H.op β δ) (H.op c S) X' η ∈ M ∧ H.IsLit M (H.label (H.op β δ) (H.op c S) X' η) l

/-- `(β, X)` is the inverse of `(δ, Y)` at the stage `α`. -/
def IsInv (M d F α δ Y β X : H.W) : Prop :=
  β ∈ α ∧ δ ∈ α ∧ δ ≠ H.emp ∧ β ≠ δ ∧ X ≠ H.emp ∧ (∀ z, z ∈ X → H.InT M F α β z) ∧
    H.IsAlt M d F α β δ X Y

/-- The pre-object `(β, D)` is retained at the stage `α`: its chain of inverses has even
length. The chain is `s`, and `K` is the set of indices at even distance from the end. -/
def Retained (M d F α β D : H.W) : Prop :=
  ∃ (n s K : H.W), n ∈ H.om ∧ H.FunOn s (H.suc n) ∧ H.App s H.emp (H.op β D) ∧
    (∀ i, i ∈ n → ∃ δ Y γ X, H.App s i (H.op δ Y) ∧ H.App s (H.suc i) (H.op γ X) ∧
      H.IsInv M d F α δ Y γ X) ∧
    (∃ δ Y, H.App s n (H.op δ Y) ∧ ¬ ∃ γ X, H.IsInv M d F α δ Y γ X) ∧
    n ∈ K ∧ H.emp ∈ K ∧ ∀ i, i ∈ n → (i ∈ K ↔ ¬ H.suc i ∈ K)

/-- The finite set `Sp` of tokens supports the pre-object `x`. -/
def SuppSet (F G α Sp x : H.W) : Prop :=
  ∀ π, π ∈ G → (∀ v, v ∈ Sp → H.App π v v) → H.ActRaw F α π x x

/-- `x` is an object of the stage `α`. -/
def IsObj (M Mp d F G α x : H.W) : Prop :=
  x ∈ Mp ∧ ∃ β D, x = H.op β D ∧
    ((D = H.emp ∧ β = H.emp) ∨
      (D ≠ H.emp ∧ β ∈ α ∧ (∀ z, z ∈ D → H.InT M F α β z) ∧ H.Retained M d F α β D)) ∧
    ∃ Sp, H.Fin Sp ∧ (∀ v, v ∈ Sp → H.IsTok M d α v) ∧ H.SuppSet F G α Sp x

/-- The tuple `S0` supports the pre-object `x`. -/
def SuppTup (F G α S0 x : H.W) : Prop :=
  ∀ π, π ∈ G → (∀ j v, H.App S0 j v → H.App π v v) → H.ActRaw F α π x x

/-- `pat` is the pattern of `x` over the sub-pool `La`: the lower level of its distinguished
extension together with the descriptors over `La` that decode into it. -/
def IsPat (M d F α La x pat : H.W) : Prop :=
  ∃ β D P0, x = H.op β D ∧ pat = H.op β P0 ∧
    ∀ e, e ∈ P0 ↔ ∃ c U z, e = H.op c U ∧ U ∈ La ∧ H.Desc M d F α β c U ∧
      H.InD M d F α β c U z ∧ z ∈ D

/-- `c` is the name of a code of the stage `α`: a tuple `S0` in the sub-pool together with the
pattern of an object that it supports. -/
def IsName (M d Λ F τ G α c : H.W) : Prop :=
  ∃ S0 pat x La, c = H.op S0 pat ∧ H.App Λ α La ∧ S0 ∈ La ∧ H.IsTup M d α S0 ∧ x ∈ τ ∧
    H.SuppTup F G α S0 x ∧ H.IsPat M d F α La x pat

/-- `π` sends the tuple `S0` to the tuple `S`, entry by entry. -/
def MapsTup (π S0 S : H.W) : Prop := ∀ j v w, H.App S0 j v → H.App S j w → H.App π v w

/-- The descriptor `(c, S)` of the stage `α` decodes to `y`. -/
def IsDec (M d Λ F τ G N α c S y : H.W) : Prop :=
  c ∈ N ∧ H.IsTup M d α S ∧ ∃ S0 pat x La, c = H.op S0 pat ∧ H.SameSig S S0 ∧ H.App Λ α La ∧
    x ∈ τ ∧ H.SuppTup F G α S0 x ∧ H.IsPat M d F α La x pat ∧
    ((∃ π, π ∈ G ∧ H.MapsTup π S0 S ∧ H.ActRaw F α π x y) ∨
      ((¬ ∃ π, π ∈ G ∧ H.MapsTup π S0 S) ∧ y = H.op H.emp H.emp))

/-- `r` is the record of the stage `α`, given the function `F` of the records of the lower
stages. -/
def StageDef (M Mp d Λ F α r : H.W) : Prop :=
  ∃ τ G A N D, r = H.op τ (H.op G (H.op A (H.op N D))) ∧
    (∀ π, π ∈ G ↔ π ∈ Mp ∧ H.IsAut M d F α π) ∧
    (∀ x, x ∈ τ ↔ H.IsObj M Mp d F G α x) ∧
    (∀ q, q ∈ A ↔ q ∈ Mp ∧ ∃ π x y, q = H.op π (H.op x y) ∧ π ∈ G ∧ x ∈ τ ∧ H.ActRaw F α π x y) ∧
    (∀ c, c ∈ N ↔ c ∈ Mp ∧ H.IsName M d Λ F τ G α c) ∧
    (∀ q, q ∈ D ↔ q ∈ Mp ∧ ∃ c S y, q = H.op c (H.op S y) ∧ H.IsDec M d Λ F τ G N α c S y)

/-- `F` is the function of the records of the stages `1, …, α`. -/
def Good (M Mp d Λ F α : H.W) : Prop :=
  H.IsFun F ∧ (∀ β r, H.App F β r → β ∈ H.suc α ∧ β ≠ H.emp) ∧
    ∀ β, β ∈ H.suc α → β ≠ H.emp → ∃ r, H.App F β r ∧ H.StageDef M Mp d Λ F β r

end Host


/-! ## The stages depend only on the lower records; existence of the records -/

namespace Host

variable (H : Host)

/-- `F` and `F'` have the same values below `α`. -/
def Agree (F F' α : H.W) : Prop := ∀ γ r, γ ∈ α → (H.App F γ r ↔ H.App F' γ r)

variable {H}

section congr

variable {M Mp d Λ F F' α : H.W} (h : H.Agree F F' α)
include h

theorem inT_congr (β z : H.W) : H.InT M F α β z ↔ H.InT M F' α β z := by
  unfold InT Rec
  refine or_congr Iff.rfl (and_congr Iff.rfl (and_congr_right fun hβ => ?_))
  simp only [h β _ hβ]

theorem inA_congr (β π x y : H.W) : H.InA F α β π x y ↔ H.InA F' α β π x y := by
  unfold InA Rec
  refine and_congr_right fun hβ => ?_
  simp only [h β _ hβ]

theorem inN_congr (β c : H.W) : H.InN F α β c ↔ H.InN F' α β c := by
  unfold InN Rec
  refine and_congr_right fun hβ => ?_
  simp only [h β _ hβ]

theorem desc_congr (γ c S : H.W) : H.Desc M d F α γ c S ↔ H.Desc M d F' α γ c S := by
  unfold Desc
  simp only [inN_congr h]

theorem inD_congr (β c S y : H.W) : H.InD M d F α β c S y ↔ H.InD M d F' α β c S y := by
  unfold InD Rec
  refine or_congr (by simp only [desc_congr h]) (and_congr Iff.rfl (and_congr_right fun hβ => ?_))
  simp only [h β _ hβ]

theorem col_congr (v γ δ c S P : H.W) :
    H.Col M d F α v γ δ c S P ↔ H.Col M d F' α v γ δ c S P := by
  unfold Col
  simp only [desc_congr h]

theorem piso_congr (θ : H.W) : H.PIso M d F α θ ↔ H.PIso M d F' α θ := by
  unfold PIso
  simp only [col_congr h]

theorem isAut_congr (π : H.W) : H.IsAut M d F α π ↔ H.IsAut M d F' α π := by
  unfold IsAut
  simp only [piso_congr h]

theorem actLow_congr (π β z z' : H.W) : H.ActLow F α π β z z' ↔ H.ActLow F' α π β z z' := by
  unfold ActLow
  simp only [inA_congr h]

theorem actRaw_congr (π x y : H.W) : H.ActRaw F α π x y ↔ H.ActRaw F' α π x y := by
  unfold ActRaw
  simp only [actLow_congr h]

theorem isAlt_congr (β δ X Y : H.W) : H.IsAlt M d F α β δ X Y ↔ H.IsAlt M d F' α β δ X Y := by
  unfold IsAlt
  simp only [desc_congr h, inD_congr h]

theorem isInv_congr (δ Y β X : H.W) : H.IsInv M d F α δ Y β X ↔ H.IsInv M d F' α δ Y β X := by
  unfold IsInv
  simp only [inT_congr h, isAlt_congr h]

theorem retained_congr (β D : H.W) : H.Retained M d F α β D ↔ H.Retained M d F' α β D := by
  unfold Retained
  simp only [isInv_congr h]

theorem suppSet_congr (G Sp x : H.W) : H.SuppSet F G α Sp x ↔ H.SuppSet F' G α Sp x := by
  unfold SuppSet
  simp only [actRaw_congr h]

theorem isObj_congr (G x : H.W) : H.IsObj M Mp d F G α x ↔ H.IsObj M Mp d F' G α x := by
  unfold IsObj
  simp only [inT_congr h, retained_congr h, suppSet_congr h]

theorem suppTup_congr (G S0 x : H.W) : H.SuppTup F G α S0 x ↔ H.SuppTup F' G α S0 x := by
  unfold SuppTup
  simp only [actRaw_congr h]

theorem isPat_congr (La x pat : H.W) : H.IsPat M d F α La x pat ↔ H.IsPat M d F' α La x pat := by
  unfold IsPat
  simp only [desc_congr h, inD_congr h]

theorem isName_congr (τ G c : H.W) : H.IsName M d Λ F τ G α c ↔ H.IsName M d Λ F' τ G α c := by
  unfold IsName
  simp only [suppTup_congr h, isPat_congr h]

theorem isDec_congr (τ G N c S y : H.W) :
    H.IsDec M d Λ F τ G N α c S y ↔ H.IsDec M d Λ F' τ G N α c S y := by
  unfold IsDec
  simp only [suppTup_congr h, isPat_congr h, actRaw_congr h]

theorem stageDef_congr (r : H.W) : H.StageDef M Mp d Λ F α r ↔ H.StageDef M Mp d Λ F' α r := by
  unfold StageDef
  simp only [isAut_congr h, isObj_congr h, actRaw_congr h, isName_congr h, isDec_congr h]

end congr

variable (H)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem def_stage (M Mp d Λ : H.W) : Def3 H (H.StageDef M Mp d Λ) := by hdef

theorem def_good (M Mp d Λ : H.W) : Def2 H (H.Good M Mp d Λ) := by
  have h := H.def_stage M Mp d Λ
  hdef

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- For every `F` there is a record for the stage `α` over `F`. -/
theorem exists_stage (M Mp d Λ F α : H.W) : ∃ r, H.StageDef M Mp d Λ F α r := by
  obtain ⟨G, hG⟩ := H.sep' Mp (fun π => H.IsAut M d F α π) (by hdef)
  obtain ⟨τ, hτ⟩ := H.sep' Mp (fun x => H.IsObj M Mp d F G α x) (by hdef)
  obtain ⟨A, hA⟩ := H.sep' Mp (fun q => ∃ π x y, q = H.op π (H.op x y) ∧ π ∈ G ∧ x ∈ τ ∧
    H.ActRaw F α π x y) (by hdef)
  obtain ⟨N, hN⟩ := H.sep' Mp (fun c => H.IsName M d Λ F τ G α c) (by hdef)
  obtain ⟨D, hD⟩ := H.sep' Mp (fun q => ∃ c S y, q = H.op c (H.op S y) ∧
    H.IsDec M d Λ F τ G N α c S y) (by hdef)
  refine ⟨_, τ, G, A, N, D, rfl, hG, fun x => ?_, hA, hN, hD⟩
  rw [hτ x]
  exact ⟨fun hx => hx.2, fun hx => ⟨hx.1, hx⟩⟩

/-- **Existence of the records.** For every number `α` there is a function `F` of the records of
the stages `1, …, α`. -/
theorem exists_good (M Mp d Λ : H.W) : ∀ α, α ∈ H.om → ∃ F, H.Good M Mp d Λ F α := by
  have hdg := H.def_good M Mp d Λ
  refine H.om_ind (fun α => ∃ F, H.Good M Mp d Λ F α) (by hdef) ?_ ?_
  · refine ⟨H.emp, H.isFun_emp, fun β r h => (H.not_mem_emp _ (H.app_iff.mp h)).elim,
      fun β hβ hβ0 => ?_⟩
    rcases H.mem_suc.mp hβ with h | h
    · exact (H.not_mem_emp β h).elim
    · exact (hβ0 h).elim
  · rintro α - ⟨F, hF, hdom, hst⟩
    obtain ⟨r, hr⟩ := H.exists_stage M Mp d Λ F (H.suc α)
    have hnew : ¬ ∃ v, H.App F (H.suc α) v := fun ⟨v, hv⟩ => H.mem_irrefl _ (hdom _ _ hv).1
    have hag : ∀ β, β ∈ H.suc α → H.Agree F (H.ins F (H.suc α) r) β := by
      intro β hβ γ r' hγ
      rw [H.app_ins]
      refine ⟨Or.inl, fun h => h.elim id fun ⟨e, _⟩ => ?_⟩
      rw [e] at hγ
      exact (H.lt_asymm (H.mem_lt _ _ hγ) (H.mem_lt _ _ hβ)).elim
    refine ⟨H.ins F (H.suc α) r, H.isFun_ins hF hnew, fun β r' h => ?_, fun β hβ hβ0 => ?_⟩
    · rcases H.app_ins.mp h with h | ⟨e, -⟩
      · exact ⟨H.mem_suc.mpr (Or.inl (hdom β r' h).1), (hdom β r' h).2⟩
      · rw [e]
        exact ⟨H.mem_suc.mpr (Or.inr rfl), H.suc_ne_emp α⟩
    · rcases H.mem_suc.mp hβ with h | h
      · obtain ⟨r', hr', hs⟩ := hst β h hβ0
        exact ⟨r', H.app_ins.mpr (Or.inl hr'), (stageDef_congr (hag β h) r').mp hs⟩
      · rw [h]
        refine ⟨r, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩), (stageDef_congr ?_ r).mp hr⟩
        intro γ r' hγ
        rw [H.app_ins]
        refine ⟨Or.inl, fun h => h.elim id fun ⟨e, _⟩ => ?_⟩
        rw [e] at hγ
        exact (H.mem_irrefl _ hγ).elim

end Host


/-! ## The tower: a ladder of closed levels with the records of all stages -/

namespace Host

/-- The data of the construction: the number `d` of proper levels, the ladder `Λ` of closed
levels, the pool level `M = Λ(d)`, the level `Mp = Λ(d+1)` of the objects, and the function `F`
of the records of the stages `1, …, d`. -/
structure Tower (H : Host) where
  d : H.W
  Λ : H.W
  M : H.W
  Mp : H.W
  F : H.W
  hd : d ∈ H.om
  hΛ : H.IsFun Λ
  lev : ∀ α, α ∈ H.suc (H.suc d) → α ≠ H.emp → ∃ La, H.App Λ α La ∧ H.Closed La
  mono : ∀ α β La Lb, H.App Λ α La → H.App Λ β Lb → α ∈ β → La ∈ Lb
  hM : H.Closed M
  hMp : H.Closed Mp
  hMd : d ≠ H.emp → H.App Λ d M
  hMpd : H.App Λ (H.suc d) Mp
  hMMp : M ∈ Mp
  good : H.Good M Mp d Λ F d

variable {H : Host} (T : Tower H)

namespace Tower

/-- `β` is a proper level. -/
def Proper (β : H.W) : Prop := β ∈ H.suc T.d ∧ β ≠ H.emp

theorem stage_ex (β : H.W) :
    ∃ τ G A N D : H.W, T.Proper β →
      H.Rec T.F β τ G A N D ∧
      (∀ π, π ∈ G ↔ π ∈ T.Mp ∧ H.IsAut T.M T.d T.F β π) ∧
      (∀ x, x ∈ τ ↔ H.IsObj T.M T.Mp T.d T.F G β x) ∧
      (∀ q, q ∈ A ↔ q ∈ T.Mp ∧ ∃ π x y, q = H.op π (H.op x y) ∧ π ∈ G ∧ x ∈ τ ∧
        H.ActRaw T.F β π x y) ∧
      (∀ c, c ∈ N ↔ c ∈ T.Mp ∧ H.IsName T.M T.d T.Λ T.F τ G β c) ∧
      (∀ q, q ∈ D ↔ q ∈ T.Mp ∧ ∃ c S y, q = H.op c (H.op S y) ∧
        H.IsDec T.M T.d T.Λ T.F τ G N β c S y) := by
  by_cases h : T.Proper β
  · obtain ⟨r, hr, τ, G, A, N, D, e, h1, h2, h3, h4, h5⟩ := T.good.2.2 β h.1 h.2
    exact ⟨τ, G, A, N, D, fun _ => ⟨by unfold Rec; rw [← e]; exact hr, h1, h2, h3, h4, h5⟩⟩
  · exact ⟨H.emp, H.emp, H.emp, H.emp, H.emp, fun h' => (h h').elim⟩

/-- The set of the objects of the proper level `β`. -/
noncomputable def Tp (β : H.W) : H.W := Classical.choose (T.stage_ex β)

/-- The set of the allowable permutations of the proper level `β`. -/
noncomputable def Gs (β : H.W) : H.W := Classical.choose (Classical.choose_spec (T.stage_ex β))

/-- The graph of the action at the proper level `β`. -/
noncomputable def As (β : H.W) : H.W :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (T.stage_ex β)))

/-- The set of the names of the codes of the proper level `β`. -/
noncomputable def Ns (β : H.W) : H.W :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (T.stage_ex β))))

/-- The graph of the decoding at the proper level `β`. -/
noncomputable def Ds (β : H.W) : H.W :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (T.stage_ex β)))))

theorem spec {β : H.W} (hβ : T.Proper β) :
    H.Rec T.F β (T.Tp β) (T.Gs β) (T.As β) (T.Ns β) (T.Ds β) ∧
      (∀ π, π ∈ T.Gs β ↔ π ∈ T.Mp ∧ H.IsAut T.M T.d T.F β π) ∧
      (∀ x, x ∈ T.Tp β ↔ H.IsObj T.M T.Mp T.d T.F (T.Gs β) β x) ∧
      (∀ q, q ∈ T.As β ↔ q ∈ T.Mp ∧ ∃ π x y, q = H.op π (H.op x y) ∧ π ∈ T.Gs β ∧ x ∈ T.Tp β ∧
        H.ActRaw T.F β π x y) ∧
      (∀ c, c ∈ T.Ns β ↔ c ∈ T.Mp ∧ H.IsName T.M T.d T.Λ T.F (T.Tp β) (T.Gs β) β c) ∧
      (∀ q, q ∈ T.Ds β ↔ q ∈ T.Mp ∧ ∃ c S y, q = H.op c (H.op S y) ∧
        H.IsDec T.M T.d T.Λ T.F (T.Tp β) (T.Gs β) (T.Ns β) β c S y) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (T.stage_ex β))))) hβ

/-- The record of a proper level is unique. -/
theorem rec_unique {β τ G A N D : H.W} (hβ : T.Proper β) (h : H.Rec T.F β τ G A N D) :
    τ = T.Tp β ∧ G = T.Gs β ∧ A = T.As β ∧ N = T.Ns β ∧ D = T.Ds β := by
  have e := T.good.1.2 _ _ _ h (T.spec hβ).1
  obtain ⟨e1, e⟩ := H.op_inj e
  obtain ⟨e2, e⟩ := H.op_inj e
  obtain ⟨e3, e⟩ := H.op_inj e
  obtain ⟨e4, e5⟩ := H.op_inj e
  exact ⟨e1, e2, e3, e4, e5⟩

/-- The set of the objects of the level `β`: the atoms at the level `0`. -/
noncomputable def Ts (β : H.W) : H.W := open Classical in if β = H.emp then H.atoms T.M else T.Tp β

theorem rec_proper {β τ G A N D : H.W} (h : H.Rec T.F β τ G A N D) : T.Proper β :=
  T.good.2.1 _ _ h

/-- Access to the objects of a lower level. -/
theorem inT_iff {α β z : H.W} (hβ : β ∈ H.suc T.d) (hβα : β ∈ α) :
    H.InT T.M T.F α β z ↔ z ∈ T.Ts β := by
  unfold InT Ts
  by_cases h0 : β = H.emp
  · simp only [h0, true_and, if_true, ne_eq, not_true_eq_false, false_and, or_false]
    exact H.mem_atoms.symm
  · simp only [h0, false_and, false_or, if_false, ne_eq, not_false_eq_true, true_and]
    constructor
    · rintro ⟨-, τ, G, A, N, D, hr, hz⟩
      rw [← (T.rec_unique (T.rec_proper hr) hr).1]
      exact hz
    · intro hz
      exact ⟨hβα, _, _, _, _, _, (T.spec ⟨hβ, h0⟩).1, hz⟩

/-- Access to the names of a lower level. -/
theorem inN_iff {α β c : H.W} (hβ : T.Proper β) (hβα : β ∈ α) :
    H.InN T.F α β c ↔ c ∈ T.Ns β := by
  unfold InN
  constructor
  · rintro ⟨-, τ, G, A, N, D, hr, hc⟩
    rw [← (T.rec_unique hβ hr).2.2.2.1]
    exact hc
  · intro hc
    exact ⟨hβα, _, _, _, _, _, (T.spec hβ).1, hc⟩

/-- Access to the action at a lower level. -/
theorem inA_iff {α β π x y : H.W} (hβ : T.Proper β) (hβα : β ∈ α) :
    H.InA T.F α β π x y ↔ H.op π (H.op x y) ∈ T.As β := by
  unfold InA
  constructor
  · rintro ⟨-, τ, G, A, N, D, hr, hc⟩
    rw [← (T.rec_unique hβ hr).2.2.1]
    exact hc
  · intro hc
    exact ⟨hβα, _, _, _, _, _, (T.spec hβ).1, hc⟩

/-- The names of a level that is not below `α` are not seen from `α`. -/
theorem inN_lt {α β c : H.W} (h : H.InN T.F α β c) : β ∈ α ∧ T.Proper β := by
  obtain ⟨hβα, τ, G, A, N, D, hr, -⟩ := h
  exact ⟨hβα, T.rec_proper hr⟩

end Tower

end Host


/-! ## Recursion along the global order restricted to a set -/

namespace Host

variable (H : Host)

/-- Induction along the global order for a definable predicate. -/
theorem lt_ind (P : H.W → Prop) (hP : Def1 H P) (h : ∀ a, (∀ b, H.lt b a → P b) → P a) :
    ∀ a, P a := by
  intro a
  by_contra hna
  obtain ⟨m, hm, hmin⟩ := H.least' (fun x => ¬ P x) (by hdef) hna
  exact hm (h m fun b hb => not_not.mp (hmin b hb))

/-- `h` is the part of `f` below `u`. -/
def IsBelow (f u h : H.W) : Prop := ∀ q, q ∈ h ↔ q ∈ f ∧ ∃ u' z, q = H.op u' z ∧ H.lt u' u

/-- `f` is the solution of the recursion with step `G` on the members of `I` below `v`. -/
def Att (G : H.W → H.W → H.W → Prop) (I f v : H.W) : Prop :=
  H.IsFun f ∧ (∀ u, (∃ z, H.App f u z) ↔ u ∈ I ∧ H.lt u v) ∧
    ∀ u z, H.App f u z → ∃ h, H.IsBelow f u h ∧ G h u z

variable {H}

theorem isBelow_unique {f u h h' : H.W} (h1 : H.IsBelow f u h) (h2 : H.IsBelow f u h') : h = h' :=
  H.ext' fun q => (h1 q).trans (h2 q).symm

theorem app_below {f u h a b : H.W} (hb : H.IsBelow f u h) :
    H.App h a b ↔ H.App f a b ∧ H.lt a u := by
  rw [H.app_iff, H.app_iff, hb]
  constructor
  · rintro ⟨h1, u', z, e, hlt⟩
    exact ⟨h1, (H.op_inj e).1 ▸ hlt⟩
  · rintro ⟨h1, hlt⟩
    exact ⟨h1, a, b, rfl, hlt⟩

section rec

variable {G : H.W → H.W → H.W → Prop} {I : H.W}
  (huniq : ∀ h v y y', G h v y → G h v y' → y = y')
include huniq

/-- Two solutions agree where both are defined. -/
theorem att_agree (hG : Def3 H G) {f f' v v' : H.W} (hf : H.Att G I f v) (hf' : H.Att G I f' v') :
    ∀ u z z', H.App f u z → H.App f' u z' → z = z' := by
  intro u
  refine H.lt_ind (fun u => ∀ z z', H.App f u z → H.App f' u z' → z = z') (by hdef) ?_ u
  intro u ih z z' hz hz'
  obtain ⟨h, hh, hGz⟩ := hf.2.2 u z hz
  obtain ⟨h', hh', hGz'⟩ := hf'.2.2 u z' hz'
  have e : h = h' := by
    refine H.ext' fun q => ?_
    rw [hh q, hh' q]
    constructor
    · rintro ⟨hq, u', w, e, hlt⟩
      have hu' : u' ∈ I := ((hf.2.1 u').mp ⟨w, H.app_iff.mpr (e ▸ hq)⟩).1
      obtain ⟨w', hw'⟩ := (hf'.2.1 u').mpr
        ⟨hu', H.lt_trans _ _ _ hlt ((hf'.2.1 u).mp ⟨z', hz'⟩).2⟩
      have := ih u' hlt w w' (H.app_iff.mpr (e ▸ hq)) hw'
      exact ⟨by rw [e, this]; exact H.app_iff.mp hw', u', w, e, hlt⟩
    · rintro ⟨hq, u', w, e, hlt⟩
      have hu' : u' ∈ I := ((hf'.2.1 u').mp ⟨w, H.app_iff.mpr (e ▸ hq)⟩).1
      obtain ⟨w', hw'⟩ := (hf.2.1 u').mpr
        ⟨hu', H.lt_trans _ _ _ hlt ((hf.2.1 u).mp ⟨z, hz⟩).2⟩
      have := ih u' hlt w' w hw' (H.app_iff.mpr (e ▸ hq))
      exact ⟨by rw [e, ← this]; exact H.app_iff.mp hw', u', w, e, hlt⟩
  rw [e] at hGz
  exact huniq _ _ _ _ hGz hGz'

/-- The solution below `v` is unique. -/
theorem att_unique (hG : Def3 H G) {f f' v : H.W} (hf : H.Att G I f v) (hf' : H.Att G I f' v) :
    f = f' := by
  refine H.ext' fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨a, b, hab⟩ := hf.1.1 q hq
    rw [H.isOp_iff.mp hab] at hq ⊢
    obtain ⟨b', hb'⟩ := (hf'.2.1 a).mpr ((hf.2.1 a).mp ⟨b, H.app_iff.mpr hq⟩)
    rw [att_agree huniq hG hf hf' a b b' (H.app_iff.mpr hq) hb']
    exact H.app_iff.mp hb'
  · obtain ⟨a, b, hab⟩ := hf'.1.1 q hq
    rw [H.isOp_iff.mp hab] at hq ⊢
    obtain ⟨b', hb'⟩ := (hf.2.1 a).mpr ((hf'.2.1 a).mp ⟨b, H.app_iff.mpr hq⟩)
    rw [← att_agree huniq hG hf hf' a b' b hb' (H.app_iff.mpr hq)]
    exact H.app_iff.mp hb'

/-- The part below `u` of a solution is the solution below `u`. -/
theorem att_below (hG : Def3 H G) {f v u h : H.W} (hf : H.Att G I f v) (hu : H.lt u v ∨ u = v)
    (hh : H.IsBelow f u h) : H.Att G I h u := by
  refine ⟨⟨fun q hq => hf.1.1 q ((hh q).mp hq).1,
    fun a b b' hb hb' => hf.1.2 a b b' ((app_below hh).mp hb).1 ((app_below hh).mp hb').1⟩,
    fun a => ?_, fun a z hz => ?_⟩
  · constructor
    · rintro ⟨z, hz⟩
      obtain ⟨hz1, hz2⟩ := (app_below hh).mp hz
      exact ⟨((hf.2.1 a).mp ⟨z, hz1⟩).1, hz2⟩
    · rintro ⟨haI, hlt⟩
      have hav : H.lt a v := hu.elim (fun h => H.lt_trans _ _ _ hlt h) (fun e => e ▸ hlt)
      obtain ⟨z, hz⟩ := (hf.2.1 a).mpr ⟨haI, hav⟩
      exact ⟨z, (app_below hh).mpr ⟨hz, hlt⟩⟩
  · obtain ⟨hz1, hz2⟩ := (app_below hh).mp hz
    obtain ⟨h', hh', hGz⟩ := hf.2.2 a z hz1
    refine ⟨h', fun q => ?_, hGz⟩
    rw [hh' q, hh q]
    constructor
    · rintro ⟨hq, u', w, e, hlt⟩
      exact ⟨⟨hq, u', w, e, H.lt_trans _ _ _ hlt hz2⟩, u', w, e, hlt⟩
    · rintro ⟨⟨hq, -⟩, u', w, e, hlt⟩
      exact ⟨hq, u', w, e, hlt⟩

/-- **Recursion.** For a definable functional step there is a solution below every `v`. -/
theorem exists_att (hG : Def3 H G) (hex : ∀ h v, ∃ y, G h v y) (I : H.W) :
    ∀ v, ∃ f, H.Att G I f v := by
  refine H.lt_ind (fun v => ∃ f, H.Att G I f v) (by hdef) ?_
  intro v ih
  obtain ⟨Iv, hIv⟩ := H.sep' I (fun u => H.lt u v) (by hdef)
  obtain ⟨g, hg⟩ := H.repl' Iv (fun u q => ∃ f y, H.Att G I f u ∧ G f u y ∧ q = H.op u y) (by hdef)
    (fun u _ q q' ⟨f, y, hf, hy, e⟩ ⟨f', y', hf', hy', e'⟩ => by
      have := att_unique huniq hG hf hf'
      rw [← this] at hy'
      rw [e, e', huniq _ _ _ _ hy hy'])
  have happ : ∀ u y, H.App g u y ↔ u ∈ I ∧ H.lt u v ∧ ∃ f, H.Att G I f u ∧ G f u y := by
    intro u y
    rw [H.app_iff, hg]
    constructor
    · rintro ⟨u', hu', f, y', hf, hy, e⟩
      obtain ⟨e1, e2⟩ := H.op_inj e
      rw [e1, e2]
      exact ⟨((hIv u').mp hu').1, ((hIv u').mp hu').2, f, hf, hy⟩
    · rintro ⟨huI, hlt, f, hf, hy⟩
      exact ⟨u, (hIv u).mpr ⟨huI, hlt⟩, f, y, hf, hy, rfl⟩
  have hgfun : H.IsFun g := by
    refine ⟨fun q hq => ?_, fun a b b' hb hb' => ?_⟩
    · obtain ⟨u, -, f, y, -, -, e⟩ := (hg q).mp hq
      exact ⟨u, y, H.isOp_iff.mpr e⟩
    · obtain ⟨-, -, f, hf, hy⟩ := (happ a b).mp hb
      obtain ⟨-, -, f', hf', hy'⟩ := (happ a b').mp hb'
      rw [← att_unique huniq hG hf hf'] at hy'
      exact huniq _ _ _ _ hy hy'
  refine ⟨g, hgfun, fun u => ?_, fun u z hz => ?_⟩
  · constructor
    · rintro ⟨z, hz⟩
      exact ⟨((happ u z).mp hz).1, ((happ u z).mp hz).2.1⟩
    · rintro ⟨huI, hlt⟩
      obtain ⟨f, hf⟩ := ih u hlt
      obtain ⟨y, hy⟩ := hex f u
      exact ⟨y, (happ u y).mpr ⟨huI, hlt, f, hf, hy⟩⟩
  · obtain ⟨huI, hlt, f, hf, hy⟩ := (happ u z).mp hz
    refine ⟨f, fun q => ?_, hy⟩
    constructor
    · intro hq
      obtain ⟨a, b, hab⟩ := hf.1.1 q hq
      rw [H.isOp_iff.mp hab] at hq ⊢
      obtain ⟨haI, hau⟩ := (hf.2.1 a).mp ⟨b, H.app_iff.mpr hq⟩
      obtain ⟨hb', hbb, hGb⟩ := hf.2.2 a b (H.app_iff.mpr hq)
      have hatt := att_below huniq hG hf (Or.inl hau) hbb
      exact ⟨H.app_iff.mp ((happ a b).mpr ⟨haI, H.lt_trans _ _ _ hau hlt, hb', hatt, hGb⟩),
        a, b, rfl, hau⟩
    · rintro ⟨hq, a, b, e, hau⟩
      rw [e] at hq ⊢
      obtain ⟨haI, -, f', hf', hy'⟩ := (happ a b).mp (H.app_iff.mpr hq)
      obtain ⟨b', hb'⟩ := (hf.2.1 a).mpr ⟨haI, hau⟩
      obtain ⟨h'', hbb, hGb⟩ := hf.2.2 a b' hb'
      have hatt := att_below huniq hG hf (Or.inl hau) hbb
      rw [att_unique huniq hG hatt hf'] at hGb
      rw [huniq _ _ _ _ hy' hGb]
      exact H.app_iff.mp hb'

/-- **Recursion on a set.** There is a function `F` on `I` such that the value at every `v` is
given by the step applied to the part of `F` below `v`. -/
theorem wo_rec (hG : Def3 H G) (hex : ∀ h v, ∃ y, G h v y) (I : H.W) :
    ∃ F, H.FunOn F I ∧ ∀ v y, H.App F v y → ∃ h, H.IsBelow F v h ∧ G h v y := by
  obtain ⟨F, hF⟩ := exists_att huniq hG hex I I
  refine ⟨F, ⟨hF.1, fun u => ?_⟩, hF.2.2⟩
  rw [hF.2.1 u]
  exact ⟨fun h => ⟨h, H.mem_lt _ _ h⟩, fun h => h.1⟩

end rec

end Host


/-! ## Partial isomorphisms of a stage: adding one vertex -/

namespace Host

variable {H : Host}

theorem op_ne_emp (a b : H.W) : H.op a b ≠ H.emp :=
  fun h => H.not_mem_emp (H.sg a) (h ▸ H.mem_up.mpr (Or.inl rfl))

theorem not_atom_of_label {t r ξ X η : H.W} (h : t = H.label r ξ X η) :
    ¬ ∃ X' η', t = H.atom X' η' :=
  fun ⟨_, _, e⟩ => H.atom_ne_label (e.symm.trans h)

theorem vertex_mem_unun {t p R : H.W} (h : H.op t p ∈ R) : t ∈ H.un (H.un R) :=
  H.mem_un.mpr ⟨H.sg t, H.mem_un.mpr ⟨H.op t p, h, H.mem_up.mpr (Or.inl rfl)⟩, H.mem_sg.mpr rfl⟩

section step

variable {M d F α θ : H.W}

/-- Adding one pair to a partial isomorphism. -/
theorem piso_ins {v w : H.W} (hθ : H.PIso M d F α θ)
    (hv : H.IsTok M d α v) (hw : H.IsTok M d α w)
    (hvd : ¬ ∃ w', H.App θ v w') (hwr : ¬ ∃ u, H.App θ u w)
    (hpk : ∀ t p t' p', v = H.op t p → w = H.op t' p' →
      p = p' ∧ ((∃ X η, t = H.atom X η) ↔ ∃ X η, t' = H.atom X η))
    (hadj1 : ∀ a p a' b b', v = H.op a p → w = H.op a' p → H.App θ (H.op b p) (H.op b' p) →
      (∃ X η, a = H.atom X η) → (∃ r ξ X η, b = H.label r ξ X η) → (H.Adj a b ↔ H.Adj a' b'))
    (hadj2 : ∀ b p b' a a', v = H.op b p → w = H.op b' p → H.App θ (H.op a p) (H.op a' p) →
      (∃ X η, a = H.atom X η) → (∃ r ξ X η, b = H.label r ξ X η) → (H.Adj a b ↔ H.Adj a' b'))
    (hcol : ∀ γ δ c S P, H.Col M d F α v γ δ c S P →
      ∃ S', H.Col M d F α w γ δ c S' P ∧ ∀ j t u, H.App S j (H.op t u) →
        ∃ t', H.App S' j (H.op t' u) ∧ H.App θ (H.op t (H.bun u P)) (H.op t' (H.bun u P)))
    (hcol' : ∀ γ δ c S' P, H.Col M d F α w γ δ c S' P → ∃ S, H.Col M d F α v γ δ c S P) :
    H.PIso M d F α (H.ins θ v w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hθ
  refine ⟨H.isFun_ins h1 hvd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rcases H.app_ins.mp hxy with h | ⟨e1, e2⟩
    · exact h2 x y h
    · rw [e1, e2]
      exact ⟨hv, hw⟩
  · intro x x' y hxy hx'y
    rcases H.app_ins.mp hxy with h | ⟨e1, e2⟩
    · rcases H.app_ins.mp hx'y with h' | ⟨e1', e2'⟩
      · exact h3 x x' y h h'
      · exact (hwr ⟨x, e2' ▸ h⟩).elim
    · rcases H.app_ins.mp hx'y with h' | ⟨e1', e2'⟩
      · exact (hwr ⟨x', e2 ▸ h'⟩).elim
      · rw [e1, e1']
  · intro t p t' p' h
    rcases H.app_ins.mp h with h | ⟨e1, e2⟩
    · exact h4 t p t' p' h
    · exact hpk t p t' p' e1.symm e2.symm
  · intro a b p a' b' ha hb hat hlab
    rcases H.app_ins.mp ha with ha | ⟨e1, e2⟩
    · rcases H.app_ins.mp hb with hb | ⟨e1', e2'⟩
      · exact h5 a b p a' b' ha hb hat hlab
      · exact hadj2 b p b' a a' e1'.symm e2'.symm ha hat hlab
    · rcases H.app_ins.mp hb with hb | ⟨e1', e2'⟩
      · exact hadj1 a p a' b b' e1.symm e2.symm hb hat hlab
      · obtain ⟨r, ξ, X, η, e⟩ := hlab
        have : a = b := (H.op_inj (e1.trans e1'.symm)).1
        exact (not_atom_of_label e (this ▸ hat)).elim
  · intro x y γ δ c S P hxy hc
    rcases H.app_ins.mp hxy with h | ⟨e1, e2⟩
    · obtain ⟨S', hS', hco⟩ := h6 x y γ δ c S P h hc
      refine ⟨S', hS', fun j t u hj => ?_⟩
      obtain ⟨t', h1', h2'⟩ := hco j t u hj
      exact ⟨t', h1', H.app_ins.mpr (Or.inl h2')⟩
    · rw [e1] at hc
      obtain ⟨S', hS', hco⟩ := hcol γ δ c S P hc
      rw [e2]
      refine ⟨S', hS', fun j t u hj => ?_⟩
      obtain ⟨t', h1', h2'⟩ := hco j t u hj
      exact ⟨t', h1', H.app_ins.mpr (Or.inl h2')⟩
  · intro x y γ δ c S' P hxy hc
    rcases H.app_ins.mp hxy with h | ⟨e1, e2⟩
    · exact h7 x y γ δ c S' P h hc
    · rw [e2] at hc
      rw [e1]
      exact hcol' γ δ c S' P hc

variable {L R Z t p : H.W}

/-- **Adding an atom.** A partial isomorphism whose range is bounded in a closed level `L`
extends to any atom token outside its domain, with a new image in `L` outside a given set. -/
theorem piso_step_atom (hL : H.Closed L) (hLM : H.Sub L M) (hθ : H.PIso M d F α θ)
    (hR : R ∈ L) (hRb : ∀ v w, H.App θ v w → w ∈ R) (hZ : Z ∈ L)
    (hv : H.IsTok M d α (H.op t p)) (hat : ∃ X η, t = H.atom X η)
    (hvd : ¬ ∃ w, H.App θ (H.op t p) w) :
    ∃ t', t' ∈ L ∧ ¬ H.op t' p ∈ Z ∧ H.PIso M d F α (H.ins θ (H.op t p) (H.op t' p)) := by
  have hU : H.un (H.un R) ∈ L := hL.un_mem (hL.un_mem hR)
  obtain ⟨P', hP'⟩ := H.sep' (H.un (H.un R)) (fun b' => ∃ b, H.App θ (H.op b p) (H.op b' p) ∧
    H.Adj t b ∧ ∃ r ξ X η, b = H.label r ξ X η) (by hdef)
  obtain ⟨N', hN'⟩ := H.sep' (H.un (H.un R)) (fun b' => ∃ b, H.App θ (H.op b p) (H.op b' p) ∧
    ¬ H.Adj t b ∧ ∃ r ξ X η, b = H.label r ξ X η) (by hdef)
  have hP'L : P' ∈ L := hL.sub _ _ (fun x hx => ((hP' x).mp hx).1) hU
  have hN'L : N' ∈ L := hL.sub _ _ (fun x hx => ((hN' x).mp hx).1) hU
  have hZv : H.bun (H.un (H.un R)) (H.un (H.un Z)) ∈ L :=
    hL.bun_mem hU (hL.un_mem (hL.un_mem hZ))
  obtain ⟨a', ha', hadj, hnadj, hfresh⟩ := hL.exists_atom hP'L hN'L hZv (fun b' h1 h2 => by
    obtain ⟨-, b1, hb1, hadj1, -⟩ := (hP' b').mp h1
    obtain ⟨-, b2, hb2, hadj2, -⟩ := (hN' b').mp h2
    have := (H.op_inj (hθ.2.2.1 _ _ _ hb1 hb2)).1
    exact hadj2 (this ▸ hadj1))
  have hw : H.IsTok M d α (H.op a' p) := by
    obtain ⟨t0, p0, e, hp, hty, -⟩ := hv
    obtain ⟨e1, e2⟩ := H.op_inj e
    exact ⟨a', p, rfl, e2 ▸ hp, e2 ▸ hty, Or.inl ⟨hLM _ ha'.1, ha'.2⟩⟩
  have hwr : ¬ ∃ u, H.App θ u (H.op a' p) := fun ⟨u, hu⟩ =>
    hfresh (H.mem_bun.mpr (Or.inl (vertex_mem_unun (hRb _ _ hu))))
  refine ⟨a', ha'.1, fun h => hfresh (H.mem_bun.mpr (Or.inr (vertex_mem_unun h))), ?_⟩
  refine piso_ins hθ hv hw hvd hwr ?_ ?_ ?_ ?_ ?_
  · intro t1 p1 t1' p1' e e'
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e1', e2'⟩ := H.op_inj e'
    exact ⟨e2.symm.trans e2', ⟨fun _ => e1' ▸ ha'.2, fun _ => e1 ▸ hat⟩⟩
  · intro a p1 a1 b b' e e' hb _ hlab
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e1', -⟩ := H.op_inj e'
    rw [← e1, ← e1']
    rw [← e2] at hb
    have hb'U : b' ∈ H.un (H.un R) := vertex_mem_unun (hRb _ _ hb)
    constructor
    · intro h
      exact hadj b' ((hP' b').mpr ⟨hb'U, b, hb, h, hlab⟩)
    · intro h
      by_contra hn
      exact hnadj b' ((hN' b').mpr ⟨hb'U, b, hb, hn, hlab⟩) h
  · intro b p1 b1 a a1 e _ _ _ hlab
    obtain ⟨r, ξ, X, η, elb⟩ := hlab
    exact (not_atom_of_label elb ((H.op_inj e).1 ▸ hat)).elim
  · rintro γ δ c S P ⟨p1, X, η, e, -⟩
    exact (not_atom_of_label (H.op_inj e).1 hat).elim
  · rintro γ δ c S P ⟨p1, X, η, e, -⟩
    exact (not_atom_of_label (H.op_inj e).1 ha'.2).elim

/-- **Adding a label without colour.** -/
theorem piso_step_flex (hL : H.Closed L) (hLM : H.Sub L M) (hθ : H.PIso M d F α θ)
    (hR : R ∈ L) (hRb : ∀ v w, H.App θ v w → w ∈ R) (hZ : Z ∈ L)
    (hv : H.IsTok M d α (H.op t p)) (hlab : ∃ r ξ X η, t = H.label r ξ X η)
    (hunc : ¬ ∃ γ δ c S P, H.Col M d F α (H.op t p) γ δ c S P)
    (hvd : ¬ ∃ w, H.App θ (H.op t p) w) :
    ∃ t', t' ∈ L ∧ ¬ H.op t' p ∈ Z ∧ H.PIso M d F α (H.ins θ (H.op t p) (H.op t' p)) := by
  have hU : H.un (H.un R) ∈ L := hL.un_mem (hL.un_mem hR)
  obtain ⟨P', hP'⟩ := H.sep' (H.un (H.un R)) (fun a' => ∃ a, H.App θ (H.op a p) (H.op a' p) ∧
    H.Adj a t ∧ ∃ X η, a = H.atom X η) (by hdef)
  obtain ⟨N', hN'⟩ := H.sep' (H.un (H.un R)) (fun a' => ∃ a, H.App θ (H.op a p) (H.op a' p) ∧
    ¬ H.Adj a t ∧ ∃ X η, a = H.atom X η) (by hdef)
  have hP'L : P' ∈ L := hL.sub _ _ (fun x hx => ((hP' x).mp hx).1) hU
  have hN'L : N' ∈ L := hL.sub _ _ (fun x hx => ((hN' x).mp hx).1) hU
  have hZv : H.bun (H.un (H.un R)) (H.un (H.un Z)) ∈ L :=
    hL.bun_mem hU (hL.un_mem (hL.un_mem hZ))
  obtain ⟨b', hb'e, hb'L, hadj, hnadj, hfresh⟩ :=
    hL.exists_label hL.emp_mem hL.emp_mem hP'L hN'L hZv (fun a' h1 h2 => by
      obtain ⟨-, a1, ha1, hadj1, -⟩ := (hP' a').mp h1
      obtain ⟨-, a2, ha2, hadj2, -⟩ := (hN' a').mp h2
      have := (H.op_inj (hθ.2.2.1 _ _ _ ha1 ha2)).1
      exact hadj2 (this ▸ hadj1))
  have hb'lab : ∃ r ξ X η, b' = H.label r ξ X η := ⟨_, _, _, _, hb'e⟩
  have hw : H.IsTok M d α (H.op b' p) := by
    obtain ⟨t0, p0, e, hp, hty, hk⟩ := hv
    obtain ⟨e1, e2⟩ := H.op_inj e
    refine ⟨b', p, rfl, e2 ▸ hp, e2 ▸ hty, Or.inr ⟨⟨hLM _ hb'L, hb'lab⟩, ?_⟩⟩
    rcases hk with hk | hk
    · obtain ⟨r, ξ, X, η, elb⟩ := hlab
      exact (not_atom_of_label elb (e1 ▸ hk.2)).elim
    · exact e2 ▸ hk.2
  have hwr : ¬ ∃ u, H.App θ u (H.op b' p) := fun ⟨u, hu⟩ =>
    hfresh (H.mem_bun.mpr (Or.inl (vertex_mem_unun (hRb _ _ hu))))
  refine ⟨b', hb'L, fun h => hfresh (H.mem_bun.mpr (Or.inr (vertex_mem_unun h))), ?_⟩
  refine piso_ins hθ hv hw hvd hwr ?_ ?_ ?_ ?_ ?_
  · intro t1 p1 t1' p1' e e'
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e1', e2'⟩ := H.op_inj e'
    obtain ⟨r, ξ, X, η, elb⟩ := hlab
    exact ⟨e2.symm.trans e2', ⟨fun h => (not_atom_of_label elb (e1 ▸ h)).elim,
      fun h => (not_atom_of_label hb'e (e1' ▸ h)).elim⟩⟩
  · intro a p1 a1 b b1 e _ _ hat _
    obtain ⟨r, ξ, X, η, elb⟩ := hlab
    exact (not_atom_of_label elb ((H.op_inj e).1 ▸ hat)).elim
  · intro b p1 b1 a a1 e e' ha hat _
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e1', -⟩ := H.op_inj e'
    rw [← e1, ← e1']
    rw [← e2] at ha
    have ha1U : a1 ∈ H.un (H.un R) := vertex_mem_unun (hRb _ _ ha)
    constructor
    · intro h
      exact hadj a1 ((hP' a1).mpr ⟨ha1U, a, ha, h, hat⟩)
    · intro h
      by_contra hn
      exact hnadj a1 ((hN' a1).mpr ⟨ha1U, a, ha, hn, hat⟩) h
  · intro γ δ c S P hc
    exact (hunc ⟨γ, δ, c, S, P, hc⟩).elim
  · rintro γ δ c S P ⟨p1, X, η, e, -⟩
    have := (H.label_inj ((H.op_inj e).1.symm.trans hb'e)).1
    exact (op_ne_emp _ _ this).elim

/-- The colour data of a token are unique. -/
theorem col_unique {v γ δ c S P γ' δ' c' S' P' : H.W} (h : H.Col M d F α v γ δ c S P)
    (h' : H.Col M d F α v γ' δ' c' S' P') : γ = γ' ∧ δ = δ' ∧ c = c' ∧ S = S' ∧ P = P' := by
  obtain ⟨p1, X1, η1, e1, -, hr1, -⟩ := h
  obtain ⟨p2, X2, η2, e2, -, hr2, -⟩ := h'
  obtain ⟨e3, e4⟩ := H.op_inj (e1.symm.trans e2)
  obtain ⟨e5, e6, -, -⟩ := H.label_inj e3
  obtain ⟨e7, e8⟩ := H.op_inj e5
  obtain ⟨e9, e10⟩ := H.op_inj e6
  refine ⟨e7, e8, e9, e10, H.ext' fun x => ?_⟩
  rw [hr1 x, hr2 x, e4, e8]

/-- **Adding a coloured label** whose coordinates are in the domain. -/
theorem piso_step_col {γ δ c S P : H.W} (hL : H.Closed L) (hLM : H.Sub L M)
    (hθ : H.PIso M d F α θ) (hR : R ∈ L) (hRb : ∀ v w, H.App θ v w → w ∈ R) (hZ : Z ∈ L)
    (hv : H.IsTok M d α (H.op t p)) (hcv : H.Col M d F α (H.op t p) γ δ c S P)
    (hcL : c ∈ L) (hγL : γ ∈ L) (hδL : δ ∈ L) (hpL : ∀ u, H.IsPath d u → u ∈ L)
    (hpar : ∀ j s u, H.App S j (H.op s u) → ∃ w, H.App θ (H.op s (H.bun u P)) w)
    (hvd : ¬ ∃ w, H.App θ (H.op t p) w) :
    ∃ t', t' ∈ L ∧ ¬ H.op t' p ∈ Z ∧ H.PIso M d F α (H.ins θ (H.op t p) (H.op t' p)) := by
  have hU : H.un (H.un R) ∈ L := hL.un_mem (hL.un_mem hR)
  -- the images of the coordinates
  have himg : ∀ j s u, H.App S j (H.op s u) →
      ∃ s', H.App θ (H.op s (H.bun u P)) (H.op s' (H.bun u P)) ∧ s' ∈ L ∧
        ((∃ X η, s = H.atom X η) ↔ ∃ X η, s' = H.atom X η) ∧
        H.IsTok M d α (H.op s' (H.bun u P)) := by
    intro j s u hj
    obtain ⟨w, hw⟩ := hpar j s u hj
    obtain ⟨s', p', e, -⟩ := (hθ.2.1 _ _ hw).2
    rw [e] at hw
    obtain ⟨ep, hk⟩ := hθ.2.2.2.1 _ _ _ _ hw
    rw [← ep] at hw
    exact ⟨s', hw, hL.trans _ _ (vertex_mem_unun (hRb _ _ hw)) hU, hk, (hθ.2.1 _ _ hw).2⟩
  -- the tuple of the images
  obtain ⟨p1, X1, η1, ev, hmin, hrest, hP0, hγδ, hγP, hdesc⟩ := hcv
  have ep : p1 = p := (H.op_inj ev).2.symm
  rw [ep] at hmin hrest
  have hSfun : ∃ n, n ∈ H.om ∧ H.FunOn S n ∧ ∀ j v, H.App S j v → ∃ s u, v = H.op s u ∧
      H.IsPath d u ∧ H.PType u γ ∧ (H.IsAtom M s ∨ (H.IsLabel M s ∧ u ≠ H.emp)) := by
    rcases hdesc with ⟨e0, k, i, -, hk, -, hSk, htok⟩ | ⟨-, -, ⟨n, hn, hSn, htok⟩, -⟩
    · refine ⟨k, hk, hSk, fun j v hj => ?_⟩
      obtain ⟨s, u, e, h1, h2, h3⟩ := htok j v hj
      exact ⟨s, u, e, h1, e0 ▸ h2, h3⟩
    · exact ⟨n, hn, hSn, fun j v hj => htok j v hj⟩
  obtain ⟨n, hn, hSn, hStok⟩ := hSfun
  have hfun : ∀ j, j ∈ n → ∀ q q', (∃ s u s', H.App S j (H.op s u) ∧
      H.App θ (H.op s (H.bun u P)) (H.op s' (H.bun u P)) ∧ q = H.op s' u) →
      (∃ s u s', H.App S j (H.op s u) ∧
      H.App θ (H.op s (H.bun u P)) (H.op s' (H.bun u P)) ∧ q' = H.op s' u) → q = q' := by
    rintro j - q q' ⟨s, u, s', h1, h2, e⟩ ⟨s2, u2, s2', h1', h2', e'⟩
    obtain ⟨e1, e2⟩ := H.op_inj (hSn.1.2 _ _ _ h1 h1')
    rw [← e1, ← e2] at h2'
    have := (H.op_inj (hθ.1.2 _ _ _ h2 h2')).1
    rw [e, e', this, e2]
  obtain ⟨S', hS'⟩ : ∃ S', S' = H.mkFun n (fun j q => ∃ s u s', H.App S j (H.op s u) ∧
      H.App θ (H.op s (H.bun u P)) (H.op s' (H.bun u P)) ∧ q = H.op s' u) (by hdef) hfun :=
    ⟨_, rfl⟩
  have happ : ∀ j q, H.App S' j q ↔ j ∈ n ∧ ∃ s u s', H.App S j (H.op s u) ∧
      H.App θ (H.op s (H.bun u P)) (H.op s' (H.bun u P)) ∧ q = H.op s' u := by
    intro j q
    rw [hS']
    exact H.app_mkFun
  have hS'n : H.FunOn S' n := by
    refine ⟨by rw [hS']; exact H.isFun_mkFun, fun j => ⟨fun hj => ?_, fun ⟨q, hq⟩ => ((happ j q).mp hq).1⟩⟩
    obtain ⟨v, hjv⟩ := (hSn.2 j).mp hj
    obtain ⟨s, u, e, -⟩ := hStok j v hjv
    rw [e] at hjv
    obtain ⟨s', hs', -⟩ := himg j s u hjv
    exact ⟨_, (happ j _).mpr ⟨hj, s, u, s', hjv, hs', rfl⟩⟩
  have hcoord : ∀ j s u, H.App S j (H.op s u) →
      ∃ s', H.App S' j (H.op s' u) ∧ H.App θ (H.op s (H.bun u P)) (H.op s' (H.bun u P)) := by
    intro j s u hj
    obtain ⟨s', hs', -⟩ := himg j s u hj
    exact ⟨s', (happ j _).mpr ⟨(hSn.2 j).mpr ⟨_, hj⟩, s, u, s', hj, hs', rfl⟩, hs'⟩
  have hS'tok : ∀ j q, H.App S' j q → ∃ s u s', H.App S j (H.op s u) ∧ q = H.op s' u ∧ s' ∈ L ∧
      H.IsPath d u ∧ H.PType u γ ∧ (H.IsAtom M s' ∨ (H.IsLabel M s' ∧ u ≠ H.emp)) ∧
      ((∃ X η, s = H.atom X η) ↔ ∃ X η, s' = H.atom X η) := by
    intro j q hq
    obtain ⟨-, s, u, s', hj, hs', e⟩ := (happ j q).mp hq
    obtain ⟨s'', hs'', hs''L, hk, htok'⟩ := himg j s u hj
    have es : s'' = s' := (H.op_inj (hθ.1.2 _ _ _ hs'' hs')).1
    rw [es] at hs''L hk htok'
    obtain ⟨s0, u0, e0, hu0, hty0, hk0⟩ := hStok j _ hj
    obtain ⟨e1, e2⟩ := H.op_inj e0
    subst e1
    subst e2
    refine ⟨s, u, s', hj, e, hs''L, hu0, hty0, ?_, hk⟩
    obtain ⟨t1, p1', e1', -, -, hk1⟩ := htok'
    obtain ⟨e3, -⟩ := H.op_inj e1'
    rw [← e3] at hk1
    rcases hk0 with hk0 | hk0
    · rcases hk1 with hk1 | hk1
      · exact Or.inl hk1
      · obtain ⟨r, ξ, X, η, elb⟩ := hk1.1.2
        exact (not_atom_of_label elb (hk.mp hk0.2)).elim
    · rcases hk1 with hk1 | hk1
      · obtain ⟨r, ξ, X, η, elb⟩ := hk0.1.2
        exact (not_atom_of_label elb (hk.mpr hk1.2)).elim
      · exact Or.inr ⟨hk1.1, hk0.2⟩
  have hS'L : S' ∈ L := hL.fun_mem hS'n (hL.nat_mem hn) (fun j q hq => by
    obtain ⟨s, u, s', -, e, hs'L, hu, -⟩ := hS'tok j q hq
    rw [e]
    exact hL.op_mem hs'L (hpL u hu))
  have hdesc' : H.Desc M d F α γ c S' := by
    rcases hdesc with ⟨e0, k, i, ec, hk, hik, hSk, htok⟩ | ⟨hγ0, hN, ⟨n1, hn1, hSn1, htok⟩, S0, pat, ec, hsig⟩
    · have ekn : k = n := H.domIs_unique hSk.2 hSn.2
      refine Or.inl ⟨e0, k, i, ec, hk, hik, ekn ▸ hS'n, fun j q hq => ?_⟩
      obtain ⟨s, u, s', -, e, -, hu, hty, hk', -⟩ := hS'tok j q hq
      exact ⟨s', u, e, hu, e0 ▸ hty, hk'⟩
    · refine Or.inr ⟨hγ0, hN, ⟨n, hn, hS'n, fun j q hq => ?_⟩, S0, pat, ec, ?_⟩
      · obtain ⟨s, u, s', -, e, -, hu, hty, hk', -⟩ := hS'tok j q hq
        exact ⟨s', u, e, hu, hty, hk'⟩
      · obtain ⟨n2, hS2, hS02, hsig'⟩ := hsig
        have en : n2 = n := H.domIs_unique hS2.2 hSn.2
        refine ⟨n, hS'n, en ▸ hS02, fun j t1 q1 t0 p0 hj hj0 => ?_⟩
        obtain ⟨s, u, s', hjS, e, -, -, -, -, hk'⟩ := hS'tok j _ hj
        obtain ⟨e1, e2⟩ := H.op_inj e
        obtain ⟨h1, h2⟩ := hsig' j s u t0 p0 hjS hj0
        exact ⟨e2.trans h1, by rw [e1]; exact hk'.symm.trans h2⟩
  -- the new label
  obtain ⟨P', hP'⟩ := H.sep' (H.un (H.un R)) (fun a' => ∃ a, H.App θ (H.op a p) (H.op a' p) ∧
    H.Adj a t ∧ ∃ X η, a = H.atom X η) (by hdef)
  obtain ⟨N', hN'⟩ := H.sep' (H.un (H.un R)) (fun a' => ∃ a, H.App θ (H.op a p) (H.op a' p) ∧
    ¬ H.Adj a t ∧ ∃ X η, a = H.atom X η) (by hdef)
  have hP'L : P' ∈ L := hL.sub _ _ (fun x hx => ((hP' x).mp hx).1) hU
  have hN'L : N' ∈ L := hL.sub _ _ (fun x hx => ((hN' x).mp hx).1) hU
  have hZv : H.bun (H.un (H.un R)) (H.un (H.un Z)) ∈ L :=
    hL.bun_mem hU (hL.un_mem (hL.un_mem hZ))
  obtain ⟨b', hb'e, hb'L, hadj, hnadj, hfresh⟩ :=
    hL.exists_label (hL.op_mem hγL hδL) (hL.op_mem hcL hS'L) hP'L hN'L hZv (fun a' h1 h2 => by
      obtain ⟨-, a1, ha1, hadj1, -⟩ := (hP' a').mp h1
      obtain ⟨-, a2, ha2, hadj2, -⟩ := (hN' a').mp h2
      have := (H.op_inj (hθ.2.2.1 _ _ _ ha1 ha2)).1
      exact hadj2 (this ▸ hadj1))
  have hb'lab : ∃ r ξ X η, b' = H.label r ξ X η := ⟨_, _, _, _, hb'e⟩
  have htlab : t = H.label (H.op γ δ) (H.op c S) X1 η1 := (H.op_inj ev).1
  have hp0 : p ≠ H.emp := fun e => hP0 (H.eq_emp fun x hx => by
    have := ((hrest x).mp hx).1
    rw [e] at this
    exact H.not_mem_emp x this)
  have hw : H.IsTok M d α (H.op b' p) := by
    obtain ⟨t0, p0, e, hp, hty, -⟩ := hv
    obtain ⟨-, e2⟩ := H.op_inj e
    exact ⟨b', p, rfl, e2 ▸ hp, e2 ▸ hty, Or.inr ⟨⟨hLM _ hb'L, hb'lab⟩, hp0⟩⟩
  have hwr : ¬ ∃ u, H.App θ u (H.op b' p) := fun ⟨u, hu⟩ =>
    hfresh (H.mem_bun.mpr (Or.inl (vertex_mem_unun (hRb _ _ hu))))
  have hcw : H.Col M d F α (H.op b' p) γ δ c S' P :=
    ⟨p, _, _, by rw [hb'e], hmin, hrest, hP0, hγδ, hγP, hdesc'⟩
  have hcv' : H.Col M d F α (H.op t p) γ δ c S P :=
    ⟨p, X1, η1, by rw [htlab], hmin, hrest, hP0, hγδ, hγP, hdesc⟩
  refine ⟨b', hb'L, fun h => hfresh (H.mem_bun.mpr (Or.inr (vertex_mem_unun h))), ?_⟩
  refine piso_ins hθ hv hw hvd hwr ?_ ?_ ?_ ?_ ?_
  · intro t1 p1 t1' p1' e e'
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e1', e2'⟩ := H.op_inj e'
    exact ⟨e2.symm.trans e2', ⟨fun h => (not_atom_of_label htlab (e1 ▸ h)).elim,
      fun h => (not_atom_of_label hb'e (e1' ▸ h)).elim⟩⟩
  · intro a p1 a1 b b1 e _ _ hat _
    exact (not_atom_of_label htlab ((H.op_inj e).1 ▸ hat)).elim
  · intro b p1 b1 a a1 e e' ha hat _
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e1', -⟩ := H.op_inj e'
    rw [← e1, ← e1']
    rw [← e2] at ha
    have ha1U : a1 ∈ H.un (H.un R) := vertex_mem_unun (hRb _ _ ha)
    constructor
    · intro h
      exact hadj a1 ((hP' a1).mpr ⟨ha1U, a, ha, h, hat⟩)
    · intro h
      by_contra hn
      exact hnadj a1 ((hN' a1).mpr ⟨ha1U, a, ha, hn, hat⟩) h
  · intro γ2 δ2 c2 S2 P2 hc2
    obtain ⟨e1, e2, e3, e4, e5⟩ := col_unique hc2 hcv'
    rw [e1, e2, e3, e4, e5]
    exact ⟨S', hcw, hcoord⟩
  · intro γ2 δ2 c2 S2 P2 hc2
    obtain ⟨e1, e2, e3, -, e5⟩ := col_unique hc2 hcw
    rw [e1, e2, e3, e5]
    exact ⟨S, hcv'⟩

end step

end Host


/-! ## Partial isomorphisms: the general step, inverses, unions of chains -/

namespace Host

variable {H : Host}

section step2

variable {M d F α θ L R Z : H.W}

/-- **Adding one vertex.** A partial isomorphism whose range is bounded in a closed level `L`
extends to any token outside its domain whose coordinates are in its domain, with a new image
in `L` outside a given set. -/
theorem piso_step {v : H.W} (hL : H.Closed L) (hLM : H.Sub L M) (hdL : H.suc d ∈ L)
    (hθ : H.PIso M d F α θ) (hR : R ∈ L) (hRb : ∀ v w, H.App θ v w → w ∈ R) (hZ : Z ∈ L)
    (hv : H.IsTok M d α v) (hvd : ¬ ∃ w, H.App θ v w)
    (hcL : ∀ γ δ c S P, H.Col M d F α v γ δ c S P → c ∈ L)
    (hpar : ∀ γ δ c S P, H.Col M d F α v γ δ c S P →
      ∀ j s u, H.App S j (H.op s u) → ∃ w, H.App θ (H.op s (H.bun u P)) w) :
    ∃ w, w ∈ L ∧ ¬ w ∈ Z ∧ H.PIso M d F α (H.ins θ v w) := by
  have hpL : ∀ u, H.IsPath d u → u ∈ L := fun u hu => hL.sub u _ (fun x hx => (hu x hx).1) hdL
  obtain ⟨t, p, e, hp, hty, hk⟩ := id hv
  subst e
  rcases hk with hk | hk
  · obtain ⟨t', ht', hZ', hθ'⟩ := piso_step_atom hL hLM hθ hR hRb hZ hv hk.2 hvd
    exact ⟨_, hL.op_mem ht' (hpL p hp), hZ', hθ'⟩
  · by_cases hc : ∃ γ δ c S P, H.Col M d F α (H.op t p) γ δ c S P
    · obtain ⟨γ, δ, c, S, P, hc⟩ := hc
      have hδ : δ ∈ L := by
        obtain ⟨p1, X, η, e, hmin, -⟩ := id hc
        rw [← (H.op_inj e).2] at hmin
        exact hL.trans _ _ (hp δ hmin.1).1 hdL
      have hγ : γ ∈ L := by
        obtain ⟨p1, X, η, e, -, hrest, hP0, -, hγP, -⟩ := id hc
        obtain ⟨x, hx⟩ := H.ne_emp hP0
        rw [← (H.op_inj e).2] at hrest
        exact hL.trans _ _ (hγP x hx) (hL.trans _ _ (hp x ((hrest x).mp hx).1).1 hdL)
      obtain ⟨t', ht', hZ', hθ'⟩ := piso_step_col hL hLM hθ hR hRb hZ hv hc
        (hcL γ δ c S P hc) hγ hδ hpL (hpar γ δ c S P hc) hvd
      exact ⟨_, hL.op_mem ht' (hpL p hp), hZ', hθ'⟩
    · obtain ⟨t', ht', hZ', hθ'⟩ := piso_step_flex hL hLM hθ hR hRb hZ hv hk.1.2 hc hvd
      exact ⟨_, hL.op_mem ht' (hpL p hp), hZ', hθ'⟩

end step2

/-- Two descriptors with the same code have tuples of the same length. -/
theorem desc_dom {M d F α γ c S S' : H.W} (h : H.Desc M d F α γ c S) (h' : H.Desc M d F α γ c S') :
    ∃ n, H.FunOn S n ∧ H.FunOn S' n := by
  rcases h with ⟨e0, k, i, ec, -, -, hS, -⟩ | ⟨h0, -, -, S0, pat, ec, n, hS, hS0, -⟩
  · rcases h' with ⟨-, k', i', ec', -, -, hS', -⟩ | ⟨h0', -⟩
    · have : k = k' := (H.op_inj (ec.symm.trans ec')).1
      exact ⟨k, hS, this ▸ hS'⟩
    · exact (h0' e0).elim
  · rcases h' with ⟨e0', -⟩ | ⟨-, -, -, S0', pat', ec', n', hS', hS0', -⟩
    · exact (h0 e0').elim
    · have e : S0 = S0' := (H.op_inj (ec.symm.trans ec')).1
      have : n = n' := H.domIs_unique hS0.2 (e ▸ hS0'.2)
      exact ⟨n, hS, this ▸ hS'⟩

/-- The inverse of a set of pairs. -/
noncomputable def inv (H : Host) (θ : H.W) : H.W :=
  H.sepS (H.prod (H.ran θ) (H.dom θ)) (fun q => ∃ v w, q = H.op w v ∧ H.App θ v w) (by hdef)

theorem app_inv {θ v w : H.W} : H.App (H.inv θ) w v ↔ H.App θ v w := by
  rw [H.app_iff]
  show H.op w v ∈ H.sepS _ _ _ ↔ _
  rw [H.mem_sepS, H.op_mem_prod, H.mem_ran, H.mem_dom]
  constructor
  · rintro ⟨-, v', w', e, h⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    rw [e1, e2]
    exact h
  · intro h
    exact ⟨⟨⟨v, h⟩, ⟨w, h⟩⟩, v, w, rfl, h⟩

theorem isFun_inv_pairs (θ : H.W) : ∀ p, p ∈ H.inv θ → ∃ a b, H.IsOp p a b := by
  intro p hp
  obtain ⟨-, v, w, e, -⟩ := H.mem_sepS.mp hp
  exact ⟨w, v, H.isOp_iff.mpr e⟩

/-- The inverse of a partial isomorphism is a partial isomorphism. -/
theorem piso_inv {M d F α θ : H.W} (hθ : H.PIso M d F α θ) : H.PIso M d F α (H.inv θ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := id hθ
  have hlab : ∀ {t p t' p'}, H.App θ (H.op t p) (H.op t' p') →
      ((∃ r ξ X η, t = H.label r ξ X η) ↔ ∃ r ξ X η, t' = H.label r ξ X η) := by
    intro t p t' p' h
    obtain ⟨-, hk⟩ := h4 t p t' p' h
    obtain ⟨⟨t0, p0, e0, -, -, hk0⟩, ⟨t1, p1, e1, -, -, hk1⟩⟩ := h2 _ _ h
    rw [← (H.op_inj e0).1] at hk0
    rw [← (H.op_inj e1).1] at hk1
    constructor
    · rintro ⟨r, ξ, X, η, e⟩
      rcases hk1 with hk1 | hk1
      · exact (not_atom_of_label e (hk.mpr hk1.2)).elim
      · exact hk1.1.2
    · rintro ⟨r, ξ, X, η, e⟩
      rcases hk0 with hk0 | hk0
      · exact (not_atom_of_label e (hk.mp hk0.2)).elim
      · exact hk0.1.2
  refine ⟨⟨isFun_inv_pairs θ, fun a b b' hb hb' => h3 b b' a (app_inv.mp hb) (app_inv.mp hb')⟩,
    fun v w h => (h2 w v (app_inv.mp h)).symm,
    fun v v' w h h' => h1.2 w v v' (app_inv.mp h) (app_inv.mp h'),
    fun t p t' p' h => ?_, fun a b p a' b' ha hb hat hl => ?_,
    fun v w γ δ c S P h hc => ?_, fun v w γ δ c S' P h hc => ?_⟩
  · obtain ⟨e, hk⟩ := h4 t' p' t p (app_inv.mp h)
    exact ⟨e.symm, hk.symm⟩
  · have ha' := app_inv.mp ha
    have hb' := app_inv.mp hb
    exact (h5 a' b' p a b ha' hb' ((h4 _ _ _ _ ha').2.mpr hat) ((hlab hb').mpr hl)).symm
  · have h' := app_inv.mp h
    obtain ⟨S0, hS0⟩ := h7 w v γ δ c S P h' hc
    obtain ⟨S1, hS1, hco⟩ := h6 w v γ δ c S0 P h' hS0
    have e : S1 = S := (col_unique hS1 hc).2.2.2.1
    rw [e] at hco
    refine ⟨S0, hS0, fun j t u hj => ?_⟩
    obtain ⟨p1, X1, η1, -, -, -, -, -, -, hd0⟩ := id hS0
    obtain ⟨p2, X2, η2, -, -, -, -, -, -, hd⟩ := id hc
    obtain ⟨n, hn0, hn⟩ := desc_dom hd0 hd
    obtain ⟨q, hq⟩ := (hn0.2 j).mp ((hn.2 j).mpr ⟨_, hj⟩)
    have hqtok : ∃ t0 u0, q = H.op t0 u0 := by
      rcases hd0 with ⟨-, k, i, -, -, -, -, htok⟩ | ⟨-, -, ⟨n1, -, -, htok⟩, -⟩
      · obtain ⟨t0, u0, e0, -⟩ := htok j q hq
        exact ⟨t0, u0, e0⟩
      · obtain ⟨t0, u0, e0, -⟩ := htok j q hq
        exact ⟨t0, u0, e0⟩
    obtain ⟨t0, u0, e0⟩ := hqtok
    rw [e0] at hq
    obtain ⟨t1, ht1, ht1'⟩ := hco j t0 u0 hq
    obtain ⟨e1, e2⟩ := H.op_inj (hn.1.2 _ _ _ ht1 hj)
    rw [e2] at hq ht1'
    rw [e1] at ht1'
    exact ⟨t0, hq, app_inv.mpr ht1'⟩
  · obtain ⟨S, hS, -⟩ := h6 w v γ δ c S' P (app_inv.mp h) hc
    exact ⟨S, hS⟩

theorem inv_sub {θ θ' : H.W} (h : H.Sub θ θ') : H.Sub (H.inv θ) (H.inv θ') := by
  intro q hq
  obtain ⟨a, b, hab⟩ := isFun_inv_pairs θ q hq
  rw [H.isOp_iff.mp hab] at hq ⊢
  exact H.app_iff.mp (app_inv.mpr (H.app_iff.mpr (h _ (H.app_iff.mp (app_inv.mp (H.app_iff.mpr hq))))))

theorem Closed.inv_mem {M θ : H.W} (hM : H.Closed M) (hθ : θ ∈ M) : H.inv θ ∈ M := by
  have h1 : H.un (H.un θ) ∈ M := hM.un_mem (hM.un_mem hθ)
  have hr : H.ran θ ∈ M := hM.sub _ _ (fun b hb => by
    obtain ⟨a, ha⟩ := H.mem_ran.mp hb
    exact H.app_mem_unun_right ha) h1
  have hd : H.dom θ ∈ M := hM.sub _ _ (fun a ha => by
    obtain ⟨b, hb⟩ := H.mem_dom.mp ha
    exact H.app_mem_unun_left hb) h1
  exact hM.sub _ _ (fun q hq => (H.mem_sepS.mp hq).1) (hM.prod_mem hr hd)

/-- The union of a chain of partial isomorphisms is a partial isomorphism. -/
theorem piso_un {M d F α C : H.W} (hch : ∀ x y, x ∈ C → y ∈ C → H.Sub x y ∨ H.Sub y x)
    (hC : ∀ x, x ∈ C → H.PIso M d F α x) : H.PIso M d F α (H.un C) := by
  have happ : ∀ {a b}, H.App (H.un C) a b ↔ ∃ x, x ∈ C ∧ H.App x a b := by
    intro a b
    rw [H.app_iff, H.mem_un]
    exact exists_congr fun x => and_congr Iff.rfl H.app_iff.symm
  have two : ∀ {a b a' b'}, H.App (H.un C) a b → H.App (H.un C) a' b' →
      ∃ x, x ∈ C ∧ H.App x a b ∧ H.App x a' b' := by
    intro a b a' b' h h'
    obtain ⟨x, hx, hab⟩ := happ.mp h
    obtain ⟨y, hy, hab'⟩ := happ.mp h'
    rcases hch x y hx hy with hs | hs
    · exact ⟨y, hy, H.app_iff.mpr (hs _ (H.app_iff.mp hab)), hab'⟩
    · exact ⟨x, hx, hab, H.app_iff.mpr (hs _ (H.app_iff.mp hab'))⟩
  refine ⟨⟨fun p hp => ?_, fun a b b' h h' => ?_⟩, fun v w h => ?_, fun v v' w h h' => ?_,
    fun t p t' p' h => ?_, fun a b p a' b' ha hb hat hl => ?_,
    fun v w γ δ c S P h hc => ?_, fun v w γ δ c S' P h hc => ?_⟩
  · obtain ⟨x, hx, hpx⟩ := H.mem_un.mp hp
    exact (hC x hx).1.1 p hpx
  · obtain ⟨x, hx, h1, h2⟩ := two h h'
    exact (hC x hx).1.2 a b b' h1 h2
  · obtain ⟨x, hx, h1⟩ := happ.mp h
    exact (hC x hx).2.1 v w h1
  · obtain ⟨x, hx, h1, h2⟩ := two h h'
    exact (hC x hx).2.2.1 v v' w h1 h2
  · obtain ⟨x, hx, h1⟩ := happ.mp h
    exact (hC x hx).2.2.2.1 t p t' p' h1
  · obtain ⟨x, hx, h1, h2⟩ := two ha hb
    exact (hC x hx).2.2.2.2.1 a b p a' b' h1 h2 hat hl
  · obtain ⟨x, hx, h1⟩ := happ.mp h
    obtain ⟨S', hS', hco⟩ := (hC x hx).2.2.2.2.2.1 v w γ δ c S P h1 hc
    refine ⟨S', hS', fun j t u hj => ?_⟩
    obtain ⟨t', ht', ht''⟩ := hco j t u hj
    exact ⟨t', ht', happ.mpr ⟨x, hx, ht''⟩⟩
  · obtain ⟨x, hx, h1⟩ := happ.mp h
    exact (hC x hx).2.2.2.2.2.2 v w γ δ c S' P h1 hc

end Host


/-! ## Extending a partial isomorphism to a token and its ancestors -/

namespace Host

variable {H : Host}

theorem isPath_mem {M d p : H.W} (hM : H.Closed M) (hdM : H.suc d ∈ M) (hp : H.IsPath d p) :
    p ∈ M :=
  hM.sub p _ (fun x hx => (hp x hx).1) hdM

theorem tok_mem {M d α v : H.W} (hM : H.Closed M) (hdM : H.suc d ∈ M) (hv : H.IsTok M d α v) :
    v ∈ M := by
  obtain ⟨t, p, e, hp, -, hk⟩ := hv
  rw [e]
  exact hM.op_mem (hk.elim (fun h => h.1) (fun h => h.1.1)) (isPath_mem hM hdM hp)

/-- The entries of the tuple of a descriptor are tokens of its level. -/
theorem desc_tok {M d F α γ c S j q : H.W} (h : H.Desc M d F α γ c S) (hj : H.App S j q) :
    H.IsTok M d γ q := by
  rcases h with ⟨e0, k, i, -, -, -, -, htok⟩ | ⟨-, -, ⟨n, -, -, htok⟩, -⟩
  · rw [e0]
    exact htok j q hj
  · exact htok j q hj

theorem desc_fun {M d F α γ c S : H.W} (h : H.Desc M d F α γ c S) :
    ∃ n, n ∈ H.om ∧ H.FunOn S n := by
  rcases h with ⟨-, k, i, -, hk, -, hS, -⟩ | ⟨-, -, ⟨n, hn, hS, -⟩, -⟩
  · exact ⟨k, hk, hS⟩
  · exact ⟨n, hn, hS⟩

/-- The coordinates of a coloured token are tokens of the same stage. -/
theorem coord_tok {M d F α v γ δ c S P j s u : H.W} (hα : α ∈ H.om) (hv : H.IsTok M d α v)
    (hc : H.Col M d F α v γ δ c S P) (hj : H.App S j (H.op s u)) :
    H.IsTok M d α (H.op s (H.bun u P)) := by
  obtain ⟨p, X, η, e, hmin, hrest, hP0, -, hγP, hdesc⟩ := hc
  obtain ⟨t0, p0, e0, hp0, hty0, -⟩ := hv
  have ep : p0 = p := (H.op_inj (e0.symm.trans e)).2
  rw [ep] at hp0 hty0
  obtain ⟨s1, u1, e1, hu, htyu, hk⟩ := desc_tok hdesc hj
  obtain ⟨e2, e3⟩ := H.op_inj e1
  subst e2
  subst e3
  have hp_ne : p ≠ H.emp := fun h => H.not_mem_emp δ (h ▸ hmin.1)
  have hαp : α ∈ p ∧ ∀ x, x ∈ p → x ∈ H.suc α := by
    rcases hty0 with h | h
    · exact (hp_ne h.1).elim
    · exact h
  have hαP : α ∈ P := by
    refine (hrest α).mpr ⟨hαp.1, fun hαδ => ?_⟩
    obtain ⟨x, hx⟩ := H.ne_emp hP0
    obtain ⟨hxp, hxδ⟩ := (hrest x).mp hx
    have h1 := hαp.2 x hxp
    have h2 := hmin.2 x hxp
    rw [hαδ] at h1
    rcases H.mem_suc.mp h1 with h1 | h1
    · rcases H.mem_suc.mp h2 with h2 | h2
      · exact H.mem_asymm h1 h2
      · exact hxδ h2.symm
    · exact hxδ h1
  have hγα : γ ∈ α := hγP α hαP
  refine ⟨s, H.bun u P, rfl, fun x hx => ?_, Or.inr ⟨H.mem_bun.mpr (Or.inr hαP), fun x hx => ?_⟩, ?_⟩
  · rcases H.mem_bun.mp hx with h | h
    · exact hu x h
    · exact hp0 x ((hrest x).mp h).1
  · rcases H.mem_bun.mp hx with h | h
    · rcases htyu with h' | h'
      · rw [h'.1] at h
        exact (H.not_mem_emp x h).elim
      · rcases H.mem_suc.mp (h'.2 x h) with h'' | h''
        · exact H.mem_suc.mpr (Or.inl (H.om_mem_trans hα hγα h''))
        · exact H.mem_suc.mpr (Or.inl (h'' ▸ hγα))
    · exact hαp.2 x ((hrest x).mp h).1
  · rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr ⟨hk.1, fun h => H.not_mem_emp α (h ▸ H.mem_bun.mpr (Or.inr hαP))⟩

/-- The vertex of a coordinate precedes the vertex of the coloured token. -/
theorem coord_lt {M d F α t p γ δ c S P j s u : H.W}
    (hc : H.Col M d F α (H.op t p) γ δ c S P) (hj : H.App S j (H.op s u)) : H.lt s t := by
  obtain ⟨p1, X, η, e, -⟩ := hc
  rw [(H.op_inj e).1]
  exact H.lt_trans _ _ _ (H.lt_op_left s u) (H.lt_trans _ _ _ (H.app_lt_right hj)
    (H.lt_trans _ _ _ (H.lt_op_right c S) (H.lt_label_xi _ _ _ _)))

/-- The coordinates of a coloured token in a closed level are in the level. -/
theorem coord_mem {M d F α t p γ δ c S P j s u Lp : H.W} (hLp : H.Closed Lp)
    (hdLp : H.suc d ∈ Lp) (hα : α ∈ H.om) (hv : H.IsTok M d α (H.op t p))
    (hvL : H.op t p ∈ Lp) (hc : H.Col M d F α (H.op t p) γ δ c S P)
    (hj : H.App S j (H.op s u)) : H.op s (H.bun u P) ∈ Lp ∧ c ∈ Lp := by
  have htok := coord_tok hα hv hc hj
  obtain ⟨p1, X, η, e, -⟩ := id hc
  have ht : t ∈ Lp := (hLp.of_op_mem hvL).1
  rw [(H.op_inj e).1] at ht
  have h1 := (hLp.of_op_mem ht).2
  have h2 := (hLp.of_op_mem h1).2
  have h3 := (hLp.of_op_mem h2).1
  have hS : S ∈ Lp := (hLp.of_op_mem h3).2
  have hsu : H.op s u ∈ Lp :=
    (hLp.of_op_mem (hLp.trans _ _ (H.app_iff.mp hj) hS)).2
  obtain ⟨s0, q0, e0, hq0, -⟩ := htok
  rw [(H.op_inj e0).2]
  exact ⟨hLp.op_mem (hLp.of_op_mem hsu).1 (isPath_mem hLp hdLp hq0), (hLp.of_op_mem h3).1⟩

section add

variable {M d F α L Lp Z : H.W}

/-- The statement of the extension lemma for the tokens with vertex `t`. -/
def AddP (M d F α L Lp Z t : H.W) : Prop :=
  ∀ p θ R, H.PIso M d F α θ → R ∈ L → (∀ v w, H.App θ v w → w ∈ R) →
    H.IsTok M d α (H.op t p) → H.op t p ∈ Lp →
    ∃ θ' R', H.PIso M d F α θ' ∧ H.Sub θ θ' ∧ R' ∈ L ∧ (∀ v w, H.App θ' v w → w ∈ R') ∧
      (∃ w, H.App θ' (H.op t p) w) ∧
      (∀ v w, H.App θ' v w → H.App θ v w ∨ (v ∈ Lp ∧ ¬ w ∈ Z ∧ (∃ s' u', v = H.op s' u' ∧ (s' = t ∨ H.lt s' t)) ∧
        (v = H.op t p ∨ ∃ v0 γ δ c S P j s u, H.Col M d F α v0 γ δ c S P ∧ H.App S j (H.op s u) ∧ v = H.op s (H.bun u P)))) ∧
      (θ ∈ M → θ' ∈ M) ∧ (H.Fin θ → H.Fin θ')

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem def_addP (M d F α L Lp Z : H.W) : Def1 H (H.AddP M d F α L Lp Z) := by hdef

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **Extension to a token.** A partial isomorphism whose range is bounded in a closed level
`L` extends to any token in the closed level `Lp`, with the new images in `L` outside `Z`, the
new arguments in `Lp`. The ancestors of the token are added first. -/
theorem addP (hM : H.Closed M) (hdM : H.suc d ∈ M) (hL : H.Closed L) (hLM : H.Sub L M)
    (hdL : H.suc d ∈ L) (hLp : H.Closed Lp) (hdLp : H.suc d ∈ Lp) (hZ : Z ∈ L) (hα : α ∈ H.om)
    (hnm : ∀ v γ δ c S P, v ∈ Lp → H.IsTok M d α v → H.Col M d F α v γ δ c S P → c ∈ L) :
    ∀ t, H.AddP M d F α L Lp Z t := by
  refine H.lt_ind _ (def_addP M d F α L Lp Z) ?_
  intro t ih p θ R hθ hR hRb hv hvL
  by_cases hdom : ∃ w, H.App θ (H.op t p) w
  · exact ⟨θ, R, hθ, fun _ h => h, hR, hRb, hdom, fun v w h => Or.inl h, id, id⟩
  -- the step from a partial isomorphism that contains the coordinates
  have final : ∀ θ1 R1, H.PIso M d F α θ1 → H.Sub θ θ1 → R1 ∈ L →
      (∀ v w, H.App θ1 v w → w ∈ R1) →
      (∀ v w, H.App θ1 v w → H.App θ v w ∨ (v ∈ Lp ∧ ¬ w ∈ Z ∧ (∃ s' u', v = H.op s' u' ∧ (s' = t ∨ H.lt s' t)) ∧
        (v = H.op t p ∨ ∃ v0 γ δ c S P j s u, H.Col M d F α v0 γ δ c S P ∧ H.App S j (H.op s u) ∧ v = H.op s (H.bun u P)))) →
      (θ ∈ M → θ1 ∈ M) → (H.Fin θ → H.Fin θ1) →
      (∀ γ δ c S P, H.Col M d F α (H.op t p) γ δ c S P →
        ∀ j s u, H.App S j (H.op s u) → ∃ w, H.App θ1 (H.op s (H.bun u P)) w) →
      ∃ θ' R', H.PIso M d F α θ' ∧ H.Sub θ θ' ∧ R' ∈ L ∧ (∀ v w, H.App θ' v w → w ∈ R') ∧
        (∃ w, H.App θ' (H.op t p) w) ∧
        (∀ v w, H.App θ' v w → H.App θ v w ∨ (v ∈ Lp ∧ ¬ w ∈ Z ∧ (∃ s' u', v = H.op s' u' ∧ (s' = t ∨ H.lt s' t)) ∧
        (v = H.op t p ∨ ∃ v0 γ δ c S P j s u, H.Col M d F α v0 γ δ c S P ∧ H.App S j (H.op s u) ∧ v = H.op s (H.bun u P)))) ∧
        (θ ∈ M → θ' ∈ M) ∧ (H.Fin θ → H.Fin θ') := by
    intro θ1 R1 hθ1 hsub hR1 hR1b hnew hM1 hF1 hpar
    by_cases hdom1 : ∃ w, H.App θ1 (H.op t p) w
    · exact ⟨θ1, R1, hθ1, hsub, hR1, hR1b, hdom1, hnew, hM1, hF1⟩
    obtain ⟨w, hwL, hwZ, hθ2⟩ := piso_step hL hLM hdL hθ1 hR1 hR1b hZ hv hdom1
      (fun γ δ c S P hc => hnm _ γ δ c S P hvL hv hc) hpar
    refine ⟨H.ins θ1 (H.op t p) w, H.bun R1 (H.sg w), hθ2,
      fun q hq => H.mem_bun.mpr (Or.inl (hsub q hq)), hL.bun_mem hR1 (hL.sg_mem hwL), ?_,
      ⟨w, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩)⟩, ?_, ?_, ?_⟩
    · intro x y hxy
      rcases H.app_ins.mp hxy with h | ⟨-, e⟩
      · exact H.mem_bun.mpr (Or.inl (hR1b x y h))
      · exact H.mem_bun.mpr (Or.inr (H.mem_sg.mpr e))
    · intro x y hxy
      rcases H.app_ins.mp hxy with h | ⟨e1, e2⟩
      · exact hnew x y h
      · rw [e1, e2]
        exact Or.inr ⟨hvL, hwZ, ⟨t, p, rfl, Or.inl rfl⟩, Or.inl rfl⟩
    · intro hθM
      exact hM.bun_mem (hM1 hθM) (hM.sg_mem (hM.op_mem (tok_mem hM hdM hv) (hLM w hwL)))
    · intro hθF
      exact H.fin_ins (hF1 hθF) _
  by_cases hc : ∃ γ δ c S P, H.Col M d F α (H.op t p) γ δ c S P
  · obtain ⟨γ, δ, c, S, P, hc⟩ := hc
    obtain ⟨p1, X1, η1, -, -, -, -, -, -, hdesc⟩ := id hc
    obtain ⟨n, hn, hSn⟩ := desc_fun hdesc
    -- add the coordinates one after the other
    have loop := H.om_ind (fun k => k ∈ H.suc n →
      ∃ θ1 R1, H.PIso M d F α θ1 ∧ H.Sub θ θ1 ∧ R1 ∈ L ∧ (∀ v w, H.App θ1 v w → w ∈ R1) ∧
        (∀ j, j ∈ k → ∀ s u, H.App S j (H.op s u) → ∃ w, H.App θ1 (H.op s (H.bun u P)) w) ∧
        (∀ v w, H.App θ1 v w → H.App θ v w ∨ (v ∈ Lp ∧ ¬ w ∈ Z ∧ (∃ s' u', v = H.op s' u' ∧ (s' = t ∨ H.lt s' t)) ∧
        (v = H.op t p ∨ ∃ v0 γ δ c S P j s u, H.Col M d F α v0 γ δ c S P ∧ H.App S j (H.op s u) ∧ v = H.op s (H.bun u P)))) ∧
        (θ ∈ M → θ1 ∈ M) ∧ (H.Fin θ → H.Fin θ1)) (by hdef)
      (fun _ => ⟨θ, R, hθ, fun _ h => h, hR, hRb, fun j hj => (H.not_mem_emp j hj).elim,
        fun v w h => Or.inl h, id, id⟩)
      (fun k hk ih' hk' => by
        have hkn : k ∈ n := by
          rcases H.mem_suc.mp hk' with h | h
          · exact H.om_mem_trans hn h (H.mem_suc.mpr (Or.inr rfl))
          · rw [← h]
            exact H.mem_suc.mpr (Or.inr rfl)
        obtain ⟨θ1, R1, hθ1, hsub1, hR1, hR1b, hcov1, hnew1, hM1, hF1⟩ :=
          ih' (H.mem_suc.mpr (Or.inl hkn))
        obtain ⟨q, hq⟩ := (hSn.2 k).mp hkn
        obtain ⟨s, u, eq, -⟩ := desc_tok hdesc hq
        rw [eq] at hq
        obtain ⟨θ2, R2, hθ2, hsub2, hR2, hR2b, hdom2, hnew2, hM2, hF2⟩ :=
          ih s (coord_lt hc hq) (H.bun u P) θ1 R1 hθ1 hR1 hR1b (coord_tok hα hv hc hq)
            (coord_mem hLp hdLp hα hv hvL hc hq).1
        refine ⟨θ2, R2, hθ2, fun x hx => hsub2 x (hsub1 x hx), hR2, hR2b, ?_, ?_,
          fun h => hM2 (hM1 h), fun h => hF2 (hF1 h)⟩
        · intro j hj s' u' hj'
          rcases H.mem_suc.mp hj with h | h
          · obtain ⟨w, hw⟩ := hcov1 j h s' u' hj'
            exact ⟨w, H.app_iff.mpr (hsub2 _ (H.app_iff.mp hw))⟩
          · rw [h] at hj'
            obtain ⟨e1, e2⟩ := H.op_inj (hSn.1.2 _ _ _ hj' hq)
            rw [e1, e2]
            exact hdom2
        · intro x y hxy
          rcases hnew2 x y hxy with h | ⟨h1, h2, ⟨s', u', e', hs'⟩, hco⟩
          · exact hnew1 x y h
          · exact Or.inr ⟨h1, h2, ⟨s', u', e', Or.inr (hs'.elim (fun e => e ▸ coord_lt hc hq)
              (fun l => H.lt_trans _ _ _ l (coord_lt hc hq)))⟩,
              Or.inr (hco.elim (fun e => ⟨_, γ, δ, c, S, P, k, s, u, hc, hq, e⟩) id)⟩)
    obtain ⟨θ1, R1, hθ1, hsub1, hR1, hR1b, hcov1, hnew1, hM1, hF1⟩ :=
      loop n hn (H.mem_suc.mpr (Or.inr rfl))
    refine final θ1 R1 hθ1 hsub1 hR1 hR1b hnew1 hM1 hF1 ?_
    intro γ2 δ2 c2 S2 P2 hc2 j s u hj
    obtain ⟨-, -, -, e4, e5⟩ := col_unique hc2 hc
    rw [e4] at hj
    rw [e5]
    exact hcov1 j ((hSn.2 j).mpr ⟨_, hj⟩) s u hj
  · exact final θ R hθ (fun _ h => h) hR hRb (fun v w h => Or.inl h) id id
      (fun γ δ c S P hc' => (hc ⟨γ, δ, c, S, P, hc'⟩).elim)

end add

end Host


/-! ## Freedom of action: partial isomorphisms extend to automorphisms -/

namespace Host

variable {H : Host}

theorem col_name_mem {M d F α v γ δ c S P Lp : H.W} (hLp : H.Closed Lp) (hvL : v ∈ Lp)
    (hc : H.Col M d F α v γ δ c S P) : c ∈ Lp := by
  obtain ⟨p1, X, η, e, -⟩ := hc
  rw [e] at hvL
  have h1 := (hLp.of_op_mem hvL).1
  have h2 := (hLp.of_op_mem h1).2
  have h3 := (hLp.of_op_mem h2).2
  exact (hLp.of_op_mem (hLp.of_op_mem h3).1).1

/-- `y` is a candidate for the stage `v` of the back-and-forth: a partial isomorphism in `M`
that contains `θ` and all earlier stages (the values of `h`) and has `v` in its domain and in
its range. -/
def FoaCand (M d F α θ h v y : H.W) : Prop :=
  y ∈ M ∧ H.PIso M d F α y ∧ H.Sub θ y ∧ (∀ u z, H.App h u z → H.Sub z y) ∧
    (∃ w, H.App y v w) ∧ ∃ u, H.App y u v

/-- The step of the back-and-forth: the least candidate, or the empty set if there is none. -/
def FoaStep (M d F α θ h v y : H.W) : Prop :=
  (H.FoaCand M d F α θ h v y ∧ ∀ y', H.lt y' y → ¬ H.FoaCand M d F α θ h v y') ∨
    ((¬ ∃ y', H.FoaCand M d F α θ h v y') ∧ y = H.emp)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem def_foaCand (M d F α θ : H.W) : Def3 H (H.FoaCand M d F α θ) := by hdef

theorem def_foaStep (M d F α θ : H.W) : Def3 H (H.FoaStep M d F α θ) := by
  have h := def_foaCand M d F α θ
  hdef

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **Freedom of action.** A partial isomorphism that is an element of the pool level extends
to an automorphism of the structure of the stage. -/
theorem foa {M d F α θ : H.W} (hM : H.Closed M) (hdM : H.suc d ∈ M) (hα : α ∈ H.om)
    (hθ : H.PIso M d F α θ) (hθM : θ ∈ M) :
    ∃ π, H.IsAut M d F α π ∧ H.Sub θ π ∧ H.Sub π M := by
  have hdc := def_foaCand M d F α θ
  have hds := def_foaStep M d F α θ
  obtain ⟨I, hI⟩ := H.sep' M (fun v => H.IsTok M d α v) (by hdef)
  have hIM : ∀ v, v ∈ I ↔ H.IsTok M d α v := fun v =>
    (hI v).trans ⟨fun h => h.2, fun h => ⟨tok_mem hM hdM h, h⟩⟩
  have huniq : ∀ h v y y', H.FoaStep M d F α θ h v y → H.FoaStep M d F α θ h v y' → y = y' := by
    rintro h v y y' (⟨hc, hl⟩ | ⟨hn, e⟩) (⟨hc', hl'⟩ | ⟨hn', e'⟩)
    · rcases H.lt_tri y y' with h1 | h1 | h1
      · exact (hl' y h1 hc).elim
      · exact h1
      · exact (hl y' h1 hc').elim
    · exact (hn' ⟨y, hc⟩).elim
    · exact (hn ⟨y', hc'⟩).elim
    · rw [e, e']
  have hex : ∀ h v, ∃ y, H.FoaStep M d F α θ h v y := by
    intro h v
    by_cases hc : ∃ y', H.FoaCand M d F α θ h v y'
    · obtain ⟨y', hy'⟩ := hc
      obtain ⟨m, hm, hmin⟩ := H.least' (fun y => H.FoaCand M d F α θ h v y) (by hdef) hy'
      exact ⟨m, Or.inl ⟨hm, hmin⟩⟩
    · exact ⟨H.emp, Or.inr ⟨hc, rfl⟩⟩
  obtain ⟨Fn, hFn, hrec⟩ := wo_rec huniq hds hex I
  -- chains
  have chain : ∀ (C : H.W), (∀ x, x ∈ C → x = θ ∨ ∃ u, u ∈ I ∧ H.App Fn u x ∧
      ∀ h, H.IsBelow Fn u h → H.FoaCand M d F α θ h u x) →
      (∀ x y, x ∈ C → y ∈ C → H.Sub x y ∨ H.Sub y x) ∧ (∀ x, x ∈ C → H.PIso M d F α x) ∧
        (∀ x, x ∈ C → x ∈ M) := by
    intro C hC
    refine ⟨fun x y hx hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rcases hC x hx with e | ⟨u, huI, hux, hcx⟩
      · rcases hC y hy with e' | ⟨u', hu'I, hu'y, hcy⟩
        · rw [e, e']
          exact Or.inl fun _ h => h
        · obtain ⟨h', hh'⟩ := H.sep' Fn (fun q => ∃ u'' z, q = H.op u'' z ∧ H.lt u'' u') (by hdef)
          rw [e]
          exact Or.inl (hcy h' hh').2.2.1
      · rcases hC y hy with e' | ⟨u', hu'I, hu'y, hcy⟩
        · obtain ⟨h', hh'⟩ := H.sep' Fn (fun q => ∃ u'' z, q = H.op u'' z ∧ H.lt u'' u) (by hdef)
          rw [e']
          exact Or.inr (hcx h' hh').2.2.1
        · obtain ⟨h1, hh1⟩ := H.sep' Fn (fun q => ∃ u'' z, q = H.op u'' z ∧ H.lt u'' u) (by hdef)
          obtain ⟨h2, hh2⟩ := H.sep' Fn (fun q => ∃ u'' z, q = H.op u'' z ∧ H.lt u'' u') (by hdef)
          rcases H.lt_tri u u' with hlt | hlt | hlt
          · exact Or.inl ((hcy h2 hh2).2.2.2.1 u x ((app_below hh2).mpr ⟨hux, hlt⟩))
          · rw [hlt] at hux
            rw [hFn.1.2 _ _ _ hux hu'y]
            exact Or.inl fun _ h => h
          · exact Or.inr ((hcx h1 hh1).2.2.2.1 u' y ((app_below hh1).mpr ⟨hu'y, hlt⟩))
    · rcases hC x hx with e | ⟨u, huI, hux, hcx⟩
      · rw [e]
        exact hθ
      · obtain ⟨h', hh'⟩ := H.sep' Fn (fun q => ∃ u'' z, q = H.op u'' z ∧ H.lt u'' u) (by hdef)
        exact (hcx h' hh').2.1
    · rcases hC x hx with e | ⟨u, huI, hux, hcx⟩
      · rw [e]
        exact hθM
      · obtain ⟨h', hh'⟩ := H.sep' Fn (fun q => ∃ u'' z, q = H.op u'' z ∧ H.lt u'' u) (by hdef)
        exact (hcx h' hh').1
  -- every stage is a candidate
  have main : ∀ v, v ∈ I → ∀ y, H.App Fn v y → ∀ h, H.IsBelow Fn v h →
      H.FoaCand M d F α θ h v y := by
    intro v
    refine H.lt_ind (fun v => v ∈ I → ∀ y, H.App Fn v y → ∀ h, (∀ q, q ∈ h ↔ q ∈ Fn ∧
      ∃ u' z, q = H.op u' z ∧ H.lt u' v) → H.FoaCand M d F α θ h v y) (by hdef) ?_ v
    intro v ih hvI y hvy h hh
    obtain ⟨h', hh', hstep⟩ := hrec v y hvy
    rw [isBelow_unique hh' hh] at hstep
    rcases hstep with ⟨hc, -⟩ | ⟨hn, -⟩
    · exact hc
    exfalso
    apply hn
    have hvtok := (hIM v).mp hvI
    have hvM : v ∈ M := tok_mem hM hdM hvtok
    -- the union of the earlier stages
    have hCmem : ∀ x, x ∈ H.bun (H.sg θ) (H.ran h) → x = θ ∨ ∃ u, u ∈ I ∧ H.App Fn u x ∧
        ∀ h, H.IsBelow Fn u h → H.FoaCand M d F α θ h u x := by
      intro x hx
      rcases H.mem_bun.mp hx with hx | hx
      · exact Or.inl (H.mem_sg.mp hx)
      · obtain ⟨u, hux⟩ := H.mem_ran.mp hx
        obtain ⟨hux', hlt⟩ := (app_below hh).mp hux
        have huI : u ∈ I := (hFn.2 u).mpr ⟨x, hux'⟩
        exact Or.inr ⟨u, huI, hux', fun h0 hh0 => ih u hlt huI x hux' h0 hh0⟩
    obtain ⟨hch, hCp, hCM⟩ := chain _ hCmem
    have hhfun : H.IsFun h := ⟨fun q hq => hFn.1.1 q ((hh q).mp hq).1,
      fun a b b' hb hb' => hFn.1.2 a b b' ((app_below hh).mp hb).1 ((app_below hh).mp hb').1⟩
    have hranM : H.ran h ∈ M := by
      refine hM.ran_mem hhfun ?_ (fun a b hab => hCM b (H.mem_bun.mpr (Or.inr (H.mem_ran.mpr ⟨a, hab⟩))))
      obtain ⟨s, hs, hsm⟩ := hM.seg v hvM
      refine hM.sub _ s (fun u hu => ?_) hs
      obtain ⟨z, hz⟩ := H.mem_dom.mp hu
      obtain ⟨hz', hlt⟩ := (app_below hh).mp hz
      have huI : u ∈ I := (hFn.2 u).mpr ⟨z, hz'⟩
      exact (hsm u).mpr ⟨tok_mem hM hdM ((hIM u).mp huI), hlt⟩
    have hCinM : H.bun (H.sg θ) (H.ran h) ∈ M := hM.bun_mem (hM.sg_mem hθM) hranM
    have hU : H.PIso M d F α (H.un (H.bun (H.sg θ) (H.ran h))) := piso_un hch hCp
    have hUM : H.un (H.bun (H.sg θ) (H.ran h)) ∈ M := hM.un_mem hCinM
    have hranbd : ∀ {x : H.W}, x ∈ M → H.ran x ∈ M := fun {x} hx =>
      hM.sub _ _ (fun b hb => by
        obtain ⟨a, ha⟩ := H.mem_ran.mp hb
        exact H.app_mem_unun_right ha) (hM.un_mem (hM.un_mem hx))
    have hadd := addP (L := M) (Lp := M) (Z := H.emp) (F := F) hM hdM hM (fun _ h => h) hdM hM hdM
      hM.emp_mem hα (fun v γ δ c S P hvL _ hc => col_name_mem hM hvL hc)
    obtain ⟨t, p, ev, -⟩ := id hvtok
    subst ev
    obtain ⟨U1, R1, hU1, hsub1, -, -, hdom1, -, hM1, -⟩ :=
      hadd t p _ (H.ran _) hU (hranbd hUM) (fun a b hab => H.mem_ran.mpr ⟨a, hab⟩) hvtok hvM
    have hU1M := hM1 hUM
    obtain ⟨U2, R2, hU2, hsub2, -, -, hdom2, -, hM2, -⟩ :=
      hadd t p _ (H.ran _) (piso_inv hU1) (hranbd (hM.inv_mem hU1M))
        (fun a b hab => H.mem_ran.mpr ⟨a, hab⟩) hvtok hvM
    have hU2M := hM2 (hM.inv_mem hU1M)
    have hsub12 : H.Sub U1 (H.inv U2) := by
      intro q hq
      obtain ⟨a, b, hab⟩ := hU1.1.1 q hq
      rw [H.isOp_iff.mp hab] at hq ⊢
      exact H.app_iff.mp (app_inv.mpr (H.app_iff.mpr (hsub2 _
        (H.app_iff.mp (app_inv.mpr (H.app_iff.mpr hq))))))
    have hsubU : ∀ x, x ∈ H.bun (H.sg θ) (H.ran h) → H.Sub x (H.inv U2) := fun x hx q hq =>
      hsub12 q (hsub1 q (H.mem_un.mpr ⟨x, hx, hq⟩))
    obtain ⟨w1, hw1⟩ := hdom1
    obtain ⟨w2, hw2⟩ := hdom2
    exact ⟨H.inv U2, hM.inv_mem hU2M, piso_inv hU2,
      hsubU θ (H.mem_bun.mpr (Or.inl (H.mem_sg.mpr rfl))),
      fun u z huz => hsubU z (H.mem_bun.mpr (Or.inr (H.mem_ran.mpr ⟨u, huz⟩))),
      ⟨w1, H.app_iff.mpr (hsub12 _ (H.app_iff.mp hw1))⟩, ⟨w2, app_inv.mpr hw2⟩⟩
  -- the union of all stages
  have hCmem : ∀ x, x ∈ H.bun (H.sg θ) (H.ran Fn) → x = θ ∨ ∃ u, u ∈ I ∧ H.App Fn u x ∧
      ∀ h, H.IsBelow Fn u h → H.FoaCand M d F α θ h u x := by
    intro x hx
    rcases H.mem_bun.mp hx with hx | hx
    · exact Or.inl (H.mem_sg.mp hx)
    · obtain ⟨u, hux⟩ := H.mem_ran.mp hx
      have huI : u ∈ I := (hFn.2 u).mpr ⟨x, hux⟩
      exact Or.inr ⟨u, huI, hux, fun h0 hh0 => main u huI x hux h0 hh0⟩
  obtain ⟨hch, hCp, hCM⟩ := chain _ hCmem
  have stage : ∀ v, H.IsTok M d α v → ∃ y, y ∈ H.bun (H.sg θ) (H.ran Fn) ∧
      (∃ w, H.App y v w) ∧ ∃ u, H.App y u v := by
    intro v hv
    obtain ⟨y, hy⟩ := (hFn.2 v).mp ((hIM v).mpr hv)
    obtain ⟨h', hh'⟩ := H.sep' Fn (fun q => ∃ u'' z, q = H.op u'' z ∧ H.lt u'' v) (by hdef)
    have hc := main v ((hIM v).mpr hv) y hy h' hh'
    exact ⟨y, H.mem_bun.mpr (Or.inr (H.mem_ran.mpr ⟨v, hy⟩)), hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  refine ⟨H.un (H.bun (H.sg θ) (H.ran Fn)), ⟨piso_un hch hCp, fun v hv => ?_, fun v hv => ?_⟩,
    fun q hq => H.mem_un.mpr ⟨θ, H.mem_bun.mpr (Or.inl (H.mem_sg.mpr rfl)), hq⟩, fun q hq => ?_⟩
  · obtain ⟨y, hyC, ⟨w, hw⟩, -⟩ := stage v hv
    exact ⟨w, H.app_iff.mpr (H.mem_un.mpr ⟨y, hyC, H.app_iff.mp hw⟩)⟩
  · obtain ⟨y, hyC, -, ⟨u, hu⟩⟩ := stage v hv
    exact ⟨u, H.app_iff.mpr (H.mem_un.mpr ⟨y, hyC, H.app_iff.mp hu⟩)⟩
  · obtain ⟨x, hx, hqx⟩ := H.mem_un.mp hq
    exact hM.trans q x hqx (hCM x hx)

end Host


/-! ## Finite closed sets and moving a token -/

namespace Host

variable {H : Host}

theorem piso_emp {M d F α : H.W} : H.PIso M d F α H.emp := by
  have hn : ∀ {a b : H.W}, ¬ H.App H.emp a b := fun h => H.not_mem_emp _ (H.app_iff.mp h)
  exact ⟨⟨fun p hp => (H.not_mem_emp p hp).elim, fun a b b' h => (hn h).elim⟩,
    fun v w h => (hn h).elim, fun v v' w h => (hn h).elim, fun t p t' p' h => (hn h).elim,
    fun a b p a' b' h => (hn h).elim, fun v w γ δ c S P h => (hn h).elim,
    fun v w γ δ c S' P h => (hn h).elim⟩

/-- The identity on a set. -/
noncomputable def idOn (H : Host) (D : H.W) : H.W :=
  H.sepS (H.prod D D) (fun q => ∃ v, q = H.op v v) (by hdef)

theorem app_idOn {D v w : H.W} : H.App (H.idOn D) v w ↔ v ∈ D ∧ w = v := by
  rw [H.app_iff]
  show H.op v w ∈ H.sepS _ _ _ ↔ _
  rw [H.mem_sepS, H.op_mem_prod]
  constructor
  · rintro ⟨⟨hv, -⟩, x, e⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    exact ⟨hv, e2.trans e1.symm⟩
  · rintro ⟨hv, e⟩
    rw [e]
    exact ⟨⟨hv, hv⟩, v, rfl⟩

theorem Closed.dom_mem {M θ : H.W} (hM : H.Closed M) (hθ : θ ∈ M) : H.dom θ ∈ M :=
  hM.sub _ _ (fun a ha => by
    obtain ⟨b, hb⟩ := H.mem_dom.mp ha
    exact H.app_mem_unun_left hb) (hM.un_mem (hM.un_mem hθ))

theorem Closed.idOn_mem {M D : H.W} (hM : H.Closed M) (hD : D ∈ M) : H.idOn D ∈ M :=
  hM.sub _ _ (fun q hq => (H.mem_sepS.mp hq).1) (hM.prod_mem hD hD)

/-- The identity on the domain of a partial isomorphism is a partial isomorphism. -/
theorem piso_id_dom {M d F α θ : H.W} (hθ : H.PIso M d F α θ) :
    H.PIso M d F α (H.idOn (H.dom θ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := id hθ
  refine ⟨⟨fun p hp => ?_, fun a b b' h h' => ?_⟩, fun v w h => ?_, fun v v' w h h' => ?_,
    fun t p t' p' h => ?_, fun a b p a' b' ha hb _ _ => ?_,
    fun v w γ δ c S P h hc => ?_, fun v w γ δ c S' P h hc => ?_⟩
  · obtain ⟨-, v, e⟩ := H.mem_sepS.mp hp
    exact ⟨v, v, H.isOp_iff.mpr e⟩
  · rw [(app_idOn.mp h).2, (app_idOn.mp h').2]
  · obtain ⟨hv, e⟩ := app_idOn.mp h
    obtain ⟨w', hw'⟩ := H.mem_dom.mp hv
    rw [e]
    exact ⟨(h2 v w' hw').1, (h2 v w' hw').1⟩
  · rw [← (app_idOn.mp h).2, ← (app_idOn.mp h').2]
  · obtain ⟨e1, e2⟩ := H.op_inj (app_idOn.mp h).2
    rw [e1, e2]
    exact ⟨rfl, Iff.rfl⟩
  · rw [(H.op_inj (app_idOn.mp ha).2).1, (H.op_inj (app_idOn.mp hb).2).1]
  · obtain ⟨hv, e⟩ := app_idOn.mp h
    obtain ⟨w', hw'⟩ := H.mem_dom.mp hv
    rw [e]
    refine ⟨S, hc, fun j t u hj => ⟨t, hj, app_idOn.mpr ⟨?_, rfl⟩⟩⟩
    obtain ⟨S', -, hco⟩ := h6 v w' γ δ c S P hw' hc
    obtain ⟨t', -, ht'⟩ := hco j t u hj
    exact H.mem_dom.mpr ⟨_, ht'⟩
  · rw [(app_idOn.mp h).2] at hc
    exact ⟨S', hc⟩

section cover

variable {M d F α L Lp Z : H.W}

/-- The statement of the covering lemma for the finite set `Sp` of tokens. -/
def CoverP (M d F α L Lp Z Sp : H.W) : Prop :=
  (∀ v, v ∈ Sp → H.IsTok M d α v ∧ v ∈ Lp) →
  ∀ θ R, H.PIso M d F α θ → R ∈ L → (∀ v w, H.App θ v w → w ∈ R) →
    ∃ θ' R', H.PIso M d F α θ' ∧ H.Sub θ θ' ∧ R' ∈ L ∧ (∀ v w, H.App θ' v w → w ∈ R') ∧
      (∀ v, v ∈ Sp → ∃ w, H.App θ' v w) ∧
      (∀ v w, H.App θ' v w → H.App θ v w ∨ (v ∈ Lp ∧ ¬ w ∈ Z ∧
        (∃ s u t p, v = H.op s u ∧ H.op t p ∈ Sp ∧ (s = t ∨ H.lt s t)) ∧
        (v ∈ Sp ∨ ∃ v0 γ δ c S P j s u, H.Col M d F α v0 γ δ c S P ∧ H.App S j (H.op s u) ∧ v = H.op s (H.bun u P)))) ∧
      (θ ∈ M → θ' ∈ M) ∧ (H.Fin θ → H.Fin θ')

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem def_coverP (M d F α L Lp Z : H.W) : Def1 H (H.CoverP M d F α L Lp Z) := by hdef

/-- **Covering.** A partial isomorphism with range bounded in `L` extends over any finite set
of tokens in `Lp`; the new arguments are in `Lp` with vertices not above those of the set, the
new images are in `L` outside `Z`. -/
theorem cover (hM : H.Closed M) (hdM : H.suc d ∈ M) (hL : H.Closed L) (hLM : H.Sub L M)
    (hdL : H.suc d ∈ L) (hLp : H.Closed Lp) (hdLp : H.suc d ∈ Lp) (hZ : Z ∈ L) (hα : α ∈ H.om)
    (hnm : ∀ v γ δ c S P, v ∈ Lp → H.IsTok M d α v → H.Col M d F α v γ δ c S P → c ∈ L) :
    ∀ Sp, H.Fin Sp → H.CoverP M d F α L Lp Z Sp := by
  refine H.fin_ind _ (def_coverP M d F α L Lp Z) ?_ ?_
  · intro _ θ R hθ hR hRb
    exact ⟨θ, R, hθ, fun _ h => h, hR, hRb, fun v hv => (H.not_mem_emp v hv).elim,
      fun v w h => Or.inl h, id, id⟩
  · intro x a _ ih hx θ R hθ hR hRb
    obtain ⟨θ1, R1, hθ1, hsub1, hR1, hR1b, hcov1, hnew1, hM1, hF1⟩ :=
      ih (fun v hv => hx v (H.mem_bun.mpr (Or.inl hv))) θ R hθ hR hRb
    obtain ⟨hatok, haL⟩ := hx a (H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl)))
    obtain ⟨t, p, e, -⟩ := id hatok
    subst e
    obtain ⟨θ2, R2, hθ2, hsub2, hR2, hR2b, hdom2, hnew2, hM2, hF2⟩ :=
      addP hM hdM hL hLM hdL hLp hdLp hZ hα hnm t p θ1 R1 hθ1 hR1 hR1b hatok haL
    refine ⟨θ2, R2, hθ2, fun q hq => hsub2 q (hsub1 q hq), hR2, hR2b, fun v hv => ?_,
      fun v w h => ?_, fun h => hM2 (hM1 h), fun h => hF2 (hF1 h)⟩
    · rcases H.mem_bun.mp hv with hv | hv
      · obtain ⟨w, hw⟩ := hcov1 v hv
        exact ⟨w, H.app_iff.mpr (hsub2 _ (H.app_iff.mp hw))⟩
      · rw [H.mem_sg.mp hv]
        exact hdom2
    · rcases hnew2 v w h with h | ⟨h1, h2, ⟨s', u', e', hs'⟩, hco⟩
      · rcases hnew1 v w h with h | ⟨h1, h2, ⟨s', u', t', p', e', ht', hs'⟩, hco⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, ⟨s', u', t', p', e', H.mem_bun.mpr (Or.inl ht'), hs'⟩,
            hco.imp (fun h => H.mem_bun.mpr (Or.inl h)) id⟩
      · exact Or.inr ⟨h1, h2, ⟨s', u', t, p, e', H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl)), hs'⟩,
          hco.imp (fun e => H.mem_bun.mpr (Or.inr (H.mem_sg.mpr e))) id⟩

end cover

/-- **Moving a token.** A token whose vertex is above the vertices of a tuple is moved by an
automorphism that fixes the entries of the tuple. -/
theorem move {M d F α S n t p : H.W} (hM : H.Closed M) (hdM : H.suc d ∈ M) (hα : α ∈ H.om)
    (hn : n ∈ H.om) (hS : H.FunOn S n) (hSt : ∀ j q, H.App S j q → H.IsTok M d α q)
    (hv : H.IsTok M d α (H.op t p)) (hlt : ∀ j s u, H.App S j (H.op s u) → H.lt s t) :
    ∃ π, H.IsAut M d F α π ∧ H.Sub π M ∧ (∀ j q, H.App S j q → H.App π q q) ∧
      ¬ H.App π (H.op t p) (H.op t p) := by
  have hnm : ∀ v γ δ c S P, v ∈ M → H.IsTok M d α v → H.Col M d F α v γ δ c S P → c ∈ M :=
    fun v γ δ c S P hvL _ hc => col_name_mem hM hvL hc
  have hfin : H.Fin (H.ran S) := ⟨n, S, hn, hS, fun z => H.mem_ran⟩
  obtain ⟨θ1, R1, hθ1, -, -, -, hcov1, hnew1, hM1, -⟩ :=
    cover (Z := H.emp) hM hdM hM (fun _ h => h) hdM hM hdM hM.emp_mem hα hnm _ hfin
      (fun v hv => by
        obtain ⟨j, hj⟩ := H.mem_ran.mp hv
        exact ⟨hSt j v hj, tok_mem hM hdM (hSt j v hj)⟩)
      H.emp H.emp piso_emp hM.emp_mem (fun v w h => (H.not_mem_emp _ (H.app_iff.mp h)).elim)
  have hθ1M := hM1 hM.emp_mem
  have hdomlt : ∀ s u, H.op s u ∈ H.dom θ1 → H.lt s t := by
    intro s u hsu
    obtain ⟨w, hw⟩ := H.mem_dom.mp hsu
    rcases hnew1 _ w hw with h | ⟨-, -, ⟨s', u', t', p', e', ht', hs'⟩, -⟩
    · exact (H.not_mem_emp _ (H.app_iff.mp h)).elim
    · obtain ⟨j, hj⟩ := H.mem_ran.mp ht'
      rw [(H.op_inj e').1]
      rcases hs' with hs' | hs'
      · rw [hs']
        exact hlt j t' p' hj
      · exact H.lt_trans _ _ _ hs' (hlt j t' p' hj)
  have hdomM : H.dom θ1 ∈ M := hM.dom_mem hθ1M
  obtain ⟨θ2, R2, hθ2, hsub2, -, -, ⟨w, hw⟩, hnew2, hM2, -⟩ :=
    addP (Z := H.sg (H.op t p)) hM hdM hM (fun _ h => h) hdM hM hdM
      (hM.sg_mem (tok_mem hM hdM hv)) hα hnm t p _ (H.dom θ1) (piso_id_dom hθ1) hdomM
      (fun a b hab => by
        obtain ⟨ha, e⟩ := app_idOn.mp hab
        rw [e]
        exact ha) hv (tok_mem hM hdM hv)
  obtain ⟨π, hπ, hsubπ, hπM⟩ := foa hM hdM hα hθ2 (hM2 (hM.idOn_mem hdomM))
  refine ⟨π, hπ, hπM, fun j q hj => ?_, fun hfix => ?_⟩
  · obtain ⟨w', hw'⟩ := hcov1 q (H.mem_ran.mpr ⟨j, hj⟩)
    exact H.app_iff.mpr (hsubπ _ (hsub2 _ (H.app_iff.mp
      (app_idOn.mpr ⟨H.mem_dom.mpr ⟨w', hw'⟩, rfl⟩))))
  · have e : w = H.op t p := hπ.1.1.2 _ _ _ (H.app_iff.mpr (hsubπ _ (H.app_iff.mp hw))) hfix
    rcases hnew2 _ w hw with h | ⟨-, h, -⟩
    · exact H.lt_irrefl t (hdomlt t p (app_idOn.mp h).1)
    · exact h (H.mem_sg.mpr e)

end Host


/-! ## Derivatives of automorphisms -/

namespace Host

variable {H : Host}

theorem bun_assoc (a b c : H.W) : H.bun (H.bun a b) c = H.bun a (H.bun b c) :=
  H.ext' fun z => by simp only [H.mem_bun, or_assoc]

theorem der_app {π α β ρ v w : H.W} (h : H.IsDer π α β ρ) :
    H.App ρ v w ↔ ∃ t u t', v = H.op t u ∧ w = H.op t' u ∧ H.PType u β ∧
      H.App π (H.op t (H.bun u (H.sg α))) (H.op t' (H.bun u (H.sg α))) := by
  rw [H.app_iff, h]
  constructor
  · rintro ⟨t, u, t', e, h1, h2⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    exact ⟨t, u, t', e1, e2, h1, h2⟩
  · rintro ⟨t, u, t', e1, e2, h1, h2⟩
    exact ⟨t, u, t', by rw [e1, e2], h1, h2⟩

theorem der_unique {π α β ρ ρ' : H.W} (h : H.IsDer π α β ρ) (h' : H.IsDer π α β ρ') : ρ = ρ' :=
  H.ext' fun q => (h q).trans (h' q).symm

theorem exists_der {M π : H.W} (hM : H.Closed M) (hπ : H.Sub π M) (α β : H.W) :
    ∃ ρ, H.IsDer π α β ρ ∧ H.Sub ρ M := by
  obtain ⟨ρ, hρ⟩ := H.sep' M (fun q => ∃ t u t', q = H.op (H.op t u) (H.op t' u) ∧ H.PType u β ∧
    H.App π (H.op t (H.bun u (H.sg α))) (H.op t' (H.bun u (H.sg α)))) (by hdef)
  refine ⟨ρ, fun q => ⟨fun h => ((hρ q).mp h).2, fun h => (hρ q).mpr ⟨?_, h⟩⟩,
    fun q h => ((hρ q).mp h).1⟩
  obtain ⟨t, u, t', e, -, happ⟩ := h
  have h1 := hM.of_op_mem (hπ _ (H.app_iff.mp happ))
  have h2 := hM.of_op_mem h1.1
  have h3 := hM.of_op_mem h1.2
  have hu : u ∈ M := hM.sub u _ (fun x hx => H.mem_bun.mpr (Or.inl hx)) h2.2
  rw [e]
  exact hM.op_mem (hM.op_mem h2.1 hu) (hM.op_mem h3.1 hu)

theorem ptype_le {β u x : H.W} (hty : H.PType u β) (hx : x ∈ u) : x ∈ H.suc β := by
  rcases hty with hty | hty
  · rw [hty.1] at hx
    exact (H.not_mem_emp x hx).elim
  · exact hty.2 x hx

theorem ptype_lt {α β u x : H.W} (hα : α ∈ H.om) (hβα : β ∈ α) (hty : H.PType u β)
    (hx : x ∈ u) : x ∈ α := by
  rcases H.mem_suc.mp (ptype_le hty hx) with h | h
  · exact H.om_mem_trans hα hβα h
  · rw [h]
    exact hβα

theorem tok_raise {M d α β t u : H.W} (hα : α ∈ H.om) (hβα : β ∈ α) (hαd : α ∈ H.suc d)
    (h : H.IsTok M d β (H.op t u)) : H.IsTok M d α (H.op t (H.bun u (H.sg α))) := by
  obtain ⟨t0, u0, e, hp, hty, hk⟩ := h
  obtain ⟨e1, e2⟩ := H.op_inj e
  rw [← e1] at hk
  rw [← e2] at hp hty hk
  have hα0 : α ≠ H.emp := fun h0 => H.not_mem_emp β (h0 ▸ hβα)
  have hαb : α ∈ H.bun u (H.sg α) := H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl))
  refine ⟨t, _, rfl, fun x hx => ?_, Or.inr ⟨hαb, fun x hx => ?_⟩, ?_⟩
  · rcases H.mem_bun.mp hx with hx | hx
    · exact hp x hx
    · rw [H.mem_sg.mp hx]
      exact ⟨hαd, hα0⟩
  · rcases H.mem_bun.mp hx with hx | hx
    · exact H.mem_suc.mpr (Or.inl (ptype_lt hα hβα hty hx))
    · exact H.mem_suc.mpr (Or.inr (H.mem_sg.mp hx))
  · rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr ⟨hk.1, fun h0 => H.not_mem_emp α (h0 ▸ hαb)⟩

theorem tok_lower {M d α β t u : H.W} (hβ0 : β ≠ H.emp) (hty : H.PType u β)
    (h : H.IsTok M d α (H.op t (H.bun u (H.sg α)))) : H.IsTok M d β (H.op t u) := by
  obtain ⟨t0, u0, e, hp, -, hk⟩ := h
  obtain ⟨e1, e2⟩ := H.op_inj e
  rw [← e1] at hk
  rw [← e2] at hp
  have hu0 : u ≠ H.emp := by
    rcases hty with h' | h'
    · exact (hβ0 h'.2).elim
    · exact fun h0 => H.not_mem_emp β (h0 ▸ h'.1)
  exact ⟨t, u, rfl, fun x hx => hp x (H.mem_bun.mpr (Or.inl hx)), hty,
    hk.elim Or.inl (fun hk => Or.inr ⟨hk.1, hu0⟩)⟩

theorem minIs_raise {α β u δ : H.W} (hα : α ∈ H.om) (hβα : β ∈ α) (hty : H.PType u β)
    (h : H.MinIs u δ) : H.MinIs (H.bun u (H.sg α)) δ := by
  refine ⟨H.mem_bun.mpr (Or.inl h.1), fun x hx => ?_⟩
  rcases H.mem_bun.mp hx with hx | hx
  · exact h.2 x hx
  · rw [H.mem_sg.mp hx]
    exact H.mem_suc.mpr (Or.inl (ptype_lt hα hβα hty h.1))

theorem rest_raise {α β u δ P : H.W} (hα : α ∈ H.om) (hβα : β ∈ α) (hty : H.PType u β)
    (hmin : H.MinIs u δ) (h : H.Rest u δ P) : H.Rest (H.bun u (H.sg α)) δ (H.bun P (H.sg α)) := by
  intro x
  rw [H.mem_bun, H.mem_bun, h x]
  constructor
  · rintro (⟨h1, h2⟩ | h1)
    · exact ⟨Or.inl h1, h2⟩
    · refine ⟨Or.inr h1, fun e => ?_⟩
      rw [H.mem_sg.mp h1] at e
      have hδα := ptype_lt hα hβα hty hmin.1
      rw [← e] at hδα
      exact H.mem_irrefl α hδα
  · rintro ⟨h1 | h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h1

theorem col_iff {M d F α t p γ δ c S P : H.W} : H.Col M d F α (H.op t p) γ δ c S P ↔
    (∃ X η, t = H.label (H.op γ δ) (H.op c S) X η) ∧ H.MinIs p δ ∧ H.Rest p δ P ∧ P ≠ H.emp ∧
      γ ≠ δ ∧ (∀ x, x ∈ P → γ ∈ x) ∧ H.Desc M d F α γ c S := by
  constructor
  · rintro ⟨p1, X, η, e, h⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    rw [← e2] at h
    exact ⟨⟨X, η, e1⟩, h⟩
  · rintro ⟨⟨X, η, e⟩, h⟩
    exact ⟨p, X, η, by rw [e], h⟩

theorem desc_stage {M d F α β γ c S : H.W} (hγβ : γ ∈ β) (hγα : γ ∈ α) :
    H.Desc M d F β γ c S ↔ H.Desc M d F α γ c S := by
  unfold Desc InN
  simp only [hγβ, hγα, true_and]

/-- The source of a colour is below the type of the path. -/
theorem gamma_lt {β u δ P γ : H.W} (hβ : β ∈ H.om) (hty : H.PType u β) (hrest : H.Rest u δ P)
    (hP0 : P ≠ H.emp) (hγP : ∀ x, x ∈ P → γ ∈ x) : γ ∈ β := by
  obtain ⟨x, hx⟩ := H.ne_emp hP0
  rcases H.mem_suc.mp (ptype_le hty ((hrest x).mp hx).1) with h | h
  · exact H.om_mem_trans hβ h (hγP x hx)
  · rw [← h]
    exact hγP x hx

theorem beta_mem_P {β u δ P : H.W} (hty : H.PType u β) (hmin : H.MinIs u δ)
    (hrest : H.Rest u δ P) (hP0 : P ≠ H.emp) : β ∈ P := by
  obtain ⟨x, hx⟩ := H.ne_emp hP0
  obtain ⟨hxu, hxδ⟩ := (hrest x).mp hx
  rcases hty with hty | hty
  · rw [hty.1] at hxu
    exact (H.not_mem_emp x hxu).elim
  · refine (hrest β).mpr ⟨hty.1, fun e => ?_⟩
    have h1 := hty.2 x hxu
    have h2 := hmin.2 x hxu
    rw [e] at h1
    rcases H.mem_suc.mp h1 with h1 | h1
    · rcases H.mem_suc.mp h2 with h2 | h2
      · exact H.mem_asymm h1 h2
      · exact hxδ h2.symm
    · exact hxδ h1

/-- The type of a coordinate path: the path of an entry of the tuple of a colour, extended by
the rest of the path of the coloured token. -/
theorem ptype_coord {M d F σ β u δ P γ c S j s w : H.W} (hβ : β ∈ H.om) (hty : H.PType u β)
    (hmin : H.MinIs u δ) (hrest : H.Rest u δ P) (hP0 : P ≠ H.emp) (hγP : ∀ x, x ∈ P → γ ∈ x)
    (hdesc : H.Desc M d F σ γ c S) (hj : H.App S j (H.op s w)) : H.PType (H.bun w P) β := by
  have hγβ := gamma_lt hβ hty hrest hP0 hγP
  refine Or.inr ⟨H.mem_bun.mpr (Or.inr (beta_mem_P hty hmin hrest hP0)), fun x hx => ?_⟩
  rcases H.mem_bun.mp hx with hx | hx
  · obtain ⟨s1, u1, e1, -, hty1, -⟩ := desc_tok hdesc hj
    rw [← (H.op_inj e1).2] at hty1
    rcases H.mem_suc.mp (ptype_le hty1 hx) with h' | h'
    · exact H.mem_suc.mpr (Or.inl (H.om_mem_trans hβ hγβ h'))
    · rw [h']
      exact H.mem_suc.mpr (Or.inl hγβ)
  · exact ptype_le hty ((hrest x).mp hx).1

/-- **Derivatives are allowable.** -/
theorem der_aut {M d F α β π ρ : H.W} (hα : α ∈ H.om) (hαd : α ∈ H.suc d) (hβα : β ∈ α)
    (hβ0 : β ≠ H.emp) (hπ : H.IsAut M d F α π) (hρ : H.IsDer π α β ρ) :
    H.IsAut M d F β ρ := by
  have hβ : β ∈ H.om := (H.om_trans α hα β hβα).1
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, htot, honto⟩ := id hπ
  -- the colour of a token of the lower stage, raised and lowered
  have craise : ∀ {t u γ δ c S P}, H.PType u β → H.Col M d F β (H.op t u) γ δ c S P →
      H.Col M d F α (H.op t (H.bun u (H.sg α))) γ δ c S (H.bun P (H.sg α)) := by
    intro t u γ δ c S P hu hc
    obtain ⟨hl, hmin, hrest, hP0, hγδ, hγP, hdesc⟩ := col_iff.mp hc
    have hγβ := gamma_lt hβ hu hrest hP0 hγP
    have hγα := H.om_mem_trans hα hβα hγβ
    refine col_iff.mpr ⟨hl, minIs_raise hα hβα hu hmin, rest_raise hα hβα hu hmin hrest,
      fun h0 => H.not_mem_emp α (h0 ▸ H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl))), hγδ,
      fun x hx => ?_, (desc_stage hγβ hγα).mp hdesc⟩
    rcases H.mem_bun.mp hx with hx | hx
    · exact hγP x hx
    · rw [H.mem_sg.mp hx]
      exact hγα
  have clower : ∀ {t t' u γ δ c S S' P P'}, H.PType u β → H.Col M d F β (H.op t u) γ δ c S P →
      H.Col M d F α (H.op t' (H.bun u (H.sg α))) γ δ c S' P' →
      H.Col M d F β (H.op t' u) γ δ c S' P := by
    intro t t' u γ δ c S S' P P' hu hc hc'
    obtain ⟨-, hmin, hrest, hP0, hγδ, hγP, -⟩ := col_iff.mp hc
    obtain ⟨hl', -, -, -, -, -, hdesc'⟩ := col_iff.mp hc'
    have hγβ := gamma_lt hβ hu hrest hP0 hγP
    exact col_iff.mpr ⟨hl', hmin, hrest, hP0, hγδ, hγP,
      (desc_stage hγβ (H.om_mem_trans hα hβα hγβ)).mpr hdesc'⟩
  refine ⟨⟨⟨fun q hq => ?_, fun a b b' hb hb' => ?_⟩, fun v w h => ?_, fun v v' w h h' => ?_,
    fun t p t' p' h => ?_, fun a b p a' b' ha hb hat hl => ?_,
    fun v w γ δ c S P h hc => ?_, fun v w γ δ c S' P h hc => ?_⟩, fun v hv => ?_, fun w hw => ?_⟩
  · obtain ⟨t, u, t', e, -⟩ := (hρ q).mp hq
    exact ⟨_, _, H.isOp_iff.mpr e⟩
  · obtain ⟨t, u, t', e1, e2, hu, hp⟩ := (der_app hρ).mp hb
    obtain ⟨t2, u2, t2', e1', e2', hu', hp'⟩ := (der_app hρ).mp hb'
    obtain ⟨e3, e4⟩ := H.op_inj (e1.symm.trans e1')
    rw [← e3, ← e4] at hp'
    rw [e2, e2', ← e4, (H.op_inj (h1.2 _ _ _ hp hp')).1]
  · obtain ⟨t, u, t', e1, e2, hu, hp⟩ := (der_app hρ).mp h
    rw [e1, e2]
    exact ⟨tok_lower hβ0 hu (h2 _ _ hp).1, tok_lower hβ0 hu (h2 _ _ hp).2⟩
  · obtain ⟨t, u, t', e1, e2, hu, hp⟩ := (der_app hρ).mp h
    obtain ⟨t2, u2, t2', e1', e2', hu', hp'⟩ := (der_app hρ).mp h'
    obtain ⟨e3, e4⟩ := H.op_inj (e2.symm.trans e2')
    rw [← e3, ← e4] at hp'
    rw [e1, e1', ← e4, (H.op_inj (h3 _ _ _ hp hp')).1]
  · obtain ⟨t0, u, t0', e1, e2, hu, hp⟩ := (der_app hρ).mp h
    obtain ⟨e3, e4⟩ := H.op_inj e1
    obtain ⟨e5, e6⟩ := H.op_inj e2
    rw [e3, e5, e4, e6]
    exact ⟨rfl, (h4 _ _ _ _ hp).2⟩
  · obtain ⟨t, u, t', e1, e2, hu, hp⟩ := (der_app hρ).mp ha
    obtain ⟨t2, u2, t2', e1', e2', hu', hp'⟩ := (der_app hρ).mp hb
    obtain ⟨e3, e4⟩ := H.op_inj e1
    obtain ⟨e5, -⟩ := H.op_inj e2
    obtain ⟨e3', e4'⟩ := H.op_inj e1'
    obtain ⟨e5', -⟩ := H.op_inj e2'
    rw [← e3, ← e4, ← e5] at hp
    rw [← e3', ← e4', ← e5'] at hp'
    exact h5 a b _ a' b' hp hp' hat hl
  · obtain ⟨t, u, t', e1, e2, hu, hp⟩ := (der_app hρ).mp h
    rw [e1] at hc
    obtain ⟨-, hmin, hrest, hP0, -, hγP, hdesc⟩ := col_iff.mp hc
    obtain ⟨S', hS', hco⟩ := h6 _ _ γ δ c S _ hp (craise hu hc)
    rw [e2]
    refine ⟨S', clower hu hc hS', fun j s w' hj => ?_⟩
    obtain ⟨s', hs', hπs⟩ := hco j s w' hj
    refine ⟨s', hs', (der_app hρ).mpr ⟨s, H.bun w' P, s', rfl, rfl,
      ptype_coord hβ hu hmin hrest hP0 hγP hdesc hj, ?_⟩⟩
    rw [bun_assoc]
    exact hπs
  · obtain ⟨t, u, t', e1, e2, hu, hp⟩ := (der_app hρ).mp h
    rw [e2] at hc
    obtain ⟨S, hS⟩ := h7 _ _ γ δ c S' _ hp (craise hu hc)
    rw [e1]
    exact ⟨S, clower hu hc hS⟩
  · obtain ⟨t, u, e, hp, hty, hk⟩ := id hv
    rw [e] at hv ⊢
    obtain ⟨w0, hw0⟩ := htot _ (tok_raise hα hβα hαd hv)
    obtain ⟨t', p', e', -⟩ := (h2 _ _ hw0).2
    rw [e'] at hw0
    have ep := (h4 _ _ _ _ hw0).1
    rw [← ep] at hw0
    exact ⟨H.op t' u, (der_app hρ).mpr ⟨t, u, t', rfl, rfl, hty, hw0⟩⟩
  · obtain ⟨t', u, e, hp, hty, hk⟩ := id hw
    rw [e] at hw ⊢
    obtain ⟨v0, hv0⟩ := honto _ (tok_raise hα hβα hαd hw)
    obtain ⟨t, p, e', -⟩ := (h2 _ _ hv0).1
    rw [e'] at hv0
    have ep := (h4 _ _ _ _ hv0).1
    rw [ep] at hv0
    exact ⟨H.op t u, (der_app hρ).mpr ⟨t, u, t', rfl, rfl, hty, hv0⟩⟩

end Host


/-! ## Composition of partial isomorphisms; the group of automorphisms -/

namespace Host

variable {H : Host}

theorem piso_label {M d F α θ t p t' p' : H.W} (hθ : H.PIso M d F α θ)
    (h : H.App θ (H.op t p) (H.op t' p')) :
    (∃ r ξ X η, t = H.label r ξ X η) ↔ ∃ r ξ X η, t' = H.label r ξ X η := by
  obtain ⟨-, h2, -, h4, -⟩ := hθ
  obtain ⟨-, hk⟩ := h4 t p t' p' h
  obtain ⟨⟨t0, p0, e0, -, -, hk0⟩, ⟨t1, p1, e1, -, -, hk1⟩⟩ := h2 _ _ h
  rw [← (H.op_inj e0).1] at hk0
  rw [← (H.op_inj e1).1] at hk1
  constructor
  · rintro ⟨r, ξ, X, η, e⟩
    rcases hk1 with hk1 | hk1
    · exact (not_atom_of_label e (hk.mpr hk1.2)).elim
    · exact hk1.1.2
  · rintro ⟨r, ξ, X, η, e⟩
    rcases hk0 with hk0 | hk0
    · exact (not_atom_of_label e (hk.mp hk0.2)).elim
    · exact hk0.1.2

/-- The image of a token under a partial isomorphism has the same path. -/
theorem piso_mid {M d F α θ t p w : H.W} (hθ : H.PIso M d F α θ) (h : H.App θ (H.op t p) w) :
    ∃ t1, w = H.op t1 p := by
  obtain ⟨t1, p1, e, -⟩ := (hθ.2.1 _ _ h).2
  rw [e] at h
  exact ⟨t1, by rw [e, (hθ.2.2.2.1 _ _ _ _ h).1]⟩

theorem piso_mid' {M d F α θ t p v : H.W} (hθ : H.PIso M d F α θ) (h : H.App θ v (H.op t p)) :
    ∃ t1, v = H.op t1 p := by
  obtain ⟨t1, p1, e, -⟩ := (hθ.2.1 _ _ h).1
  rw [e] at h
  exact ⟨t1, by rw [e, (hθ.2.2.2.1 _ _ _ _ h).1]⟩

/-- The composite: first `π`, then `σ`. -/
noncomputable def comp (H : Host) (σ π : H.W) : H.W :=
  H.sepS (H.prod (H.dom π) (H.ran σ))
    (fun q => ∃ v z w, q = H.op v w ∧ H.App π v z ∧ H.App σ z w) (by hdef)

theorem app_comp {σ π v w : H.W} : H.App (H.comp σ π) v w ↔ ∃ z, H.App π v z ∧ H.App σ z w := by
  rw [H.app_iff]
  show H.op v w ∈ H.sepS _ _ _ ↔ _
  rw [H.mem_sepS, H.op_mem_prod, H.mem_dom, H.mem_ran]
  constructor
  · rintro ⟨-, v', z, w', e, h1, h2⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    rw [e1, e2]
    exact ⟨z, h1, h2⟩
  · rintro ⟨z, h1, h2⟩
    exact ⟨⟨⟨z, h1⟩, ⟨z, h2⟩⟩, v, z, w, rfl, h1, h2⟩

theorem comp_pairs (σ π : H.W) : ∀ q, q ∈ H.comp σ π → ∃ a b, H.IsOp q a b := by
  intro q hq
  obtain ⟨-, v, z, w, e, -⟩ := H.mem_sepS.mp hq
  exact ⟨v, w, H.isOp_iff.mpr e⟩

theorem piso_comp {M d F α π σ : H.W} (hπ : H.PIso M d F α π) (hσ : H.PIso M d F α σ) :
    H.PIso M d F α (H.comp σ π) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := id hπ
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := id hσ
  refine ⟨⟨comp_pairs σ π, fun a b b' h h' => ?_⟩, fun v w h => ?_, fun v v' w h h' => ?_,
    fun t p t' p' h => ?_, fun a b p a' b' ha hb hat hl => ?_,
    fun v w γ δ c S P h hc => ?_, fun v w γ δ c S' P h hc => ?_⟩
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    obtain ⟨z', hz1', hz2'⟩ := app_comp.mp h'
    rw [h1.2 _ _ _ hz1 hz1'] at hz2
    exact k1.2 _ _ _ hz2 hz2'
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    exact ⟨(h2 _ _ hz1).1, (k2 _ _ hz2).2⟩
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    obtain ⟨z', hz1', hz2'⟩ := app_comp.mp h'
    rw [k3 _ _ _ hz2 hz2'] at hz1
    exact h3 _ _ _ hz1 hz1'
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    obtain ⟨t1, e⟩ := piso_mid hπ hz1
    rw [e] at hz1 hz2
    exact ⟨(k4 _ _ _ _ hz2).1, (h4 _ _ _ _ hz1).2.trans (k4 _ _ _ _ hz2).2⟩
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp ha
    obtain ⟨z', hz1', hz2'⟩ := app_comp.mp hb
    obtain ⟨a1, e⟩ := piso_mid hπ hz1
    obtain ⟨b1, e'⟩ := piso_mid hπ hz1'
    rw [e] at hz1 hz2
    rw [e'] at hz1' hz2'
    exact (h5 a b p a1 b1 hz1 hz1' hat hl).trans
      (k5 a1 b1 p a' b' hz2 hz2' ((h4 _ _ _ _ hz1).2.mp hat) ((piso_label hπ hz1').mp hl))
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    obtain ⟨S1, hS1, hco1⟩ := h6 v z γ δ c S P hz1 hc
    obtain ⟨S2, hS2, hco2⟩ := k6 z w γ δ c S1 P hz2 hS1
    refine ⟨S2, hS2, fun j t u hj => ?_⟩
    obtain ⟨t1, ht1, hπ1⟩ := hco1 j t u hj
    obtain ⟨t2, ht2, hσ2⟩ := hco2 j t1 u ht1
    exact ⟨t2, ht2, app_comp.mpr ⟨_, hπ1, hσ2⟩⟩
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    obtain ⟨S1, hS1⟩ := k7 z w γ δ c S' P hz2 hc
    exact h7 v z γ δ c S1 P hz1 hS1

theorem isAut_comp {M d F α π σ : H.W} (hπ : H.IsAut M d F α π) (hσ : H.IsAut M d F α σ) :
    H.IsAut M d F α (H.comp σ π) := by
  refine ⟨piso_comp hπ.1 hσ.1, fun v hv => ?_, fun w hw => ?_⟩
  · obtain ⟨z, hz⟩ := hπ.2.1 v hv
    obtain ⟨w, hw⟩ := hσ.2.1 z (hπ.1.2.1 _ _ hz).2
    exact ⟨w, app_comp.mpr ⟨z, hz, hw⟩⟩
  · obtain ⟨z, hz⟩ := hσ.2.2 w hw
    obtain ⟨v, hv⟩ := hπ.2.2 z (hσ.1.2.1 _ _ hz).1
    exact ⟨v, app_comp.mpr ⟨z, hv, hz⟩⟩

theorem isAut_inv {M d F α π : H.W} (hπ : H.IsAut M d F α π) : H.IsAut M d F α (H.inv π) :=
  ⟨piso_inv hπ.1, fun v hv => (hπ.2.2 v hv).imp fun _ h => app_inv.mpr h,
    fun w hw => (hπ.2.1 w hw).imp fun _ h => app_inv.mpr h⟩

theorem inv_inv {π : H.W} (hp : ∀ q, q ∈ π → ∃ a b, H.IsOp q a b) : H.inv (H.inv π) = π := by
  refine H.ext' fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨a, b, hab⟩ := isFun_inv_pairs _ q hq
    rw [H.isOp_iff.mp hab] at hq ⊢
    exact H.app_iff.mp (app_inv.mp (app_inv.mp (H.app_iff.mpr hq)))
  · obtain ⟨a, b, hab⟩ := hp q hq
    rw [H.isOp_iff.mp hab] at hq ⊢
    exact H.app_iff.mp (app_inv.mpr (app_inv.mpr (H.app_iff.mpr hq)))

/-- An automorphism is a subset of the pool level. -/
theorem aut_sub {M d F α π : H.W} (hM : H.Closed M) (hdM : H.suc d ∈ M)
    (hπ : H.PIso M d F α π) : H.Sub π M := by
  intro q hq
  obtain ⟨a, b, hab⟩ := hπ.1.1 q hq
  rw [H.isOp_iff.mp hab] at hq ⊢
  obtain ⟨ha, hb⟩ := hπ.2.1 a b (H.app_iff.mpr hq)
  exact hM.op_mem (tok_mem hM hdM ha) (tok_mem hM hdM hb)

theorem isDer_of_app {π α β ρ : H.W} (hp : ∀ q, q ∈ ρ → ∃ a b, H.IsOp q a b)
    (h : ∀ v w, H.App ρ v w ↔ ∃ t u t', v = H.op t u ∧ w = H.op t' u ∧ H.PType u β ∧
      H.App π (H.op t (H.bun u (H.sg α))) (H.op t' (H.bun u (H.sg α)))) : H.IsDer π α β ρ := by
  intro q
  constructor
  · intro hq
    obtain ⟨a, b, hab⟩ := hp q hq
    rw [H.isOp_iff.mp hab] at hq ⊢
    obtain ⟨t, u, t', e1, e2, h1, h2⟩ := (h a b).mp (H.app_iff.mpr hq)
    exact ⟨t, u, t', by rw [e1, e2], h1, h2⟩
  · rintro ⟨t, u, t', e, h1, h2⟩
    rw [e]
    exact H.app_iff.mp ((h _ _).mpr ⟨t, u, t', rfl, rfl, h1, h2⟩)

theorem der_comp {M d F α β π σ ρ ρ' : H.W} (hπ : H.PIso M d F α π)
    (hρ : H.IsDer π α β ρ) (hρ' : H.IsDer σ α β ρ') :
    H.IsDer (H.comp σ π) α β (H.comp ρ' ρ) := by
  refine isDer_of_app (comp_pairs ρ' ρ) fun v w => ?_
  rw [app_comp]
  constructor
  · rintro ⟨z, hz1, hz2⟩
    obtain ⟨t, u, t1, e1, e2, hu, hp⟩ := (der_app hρ).mp hz1
    obtain ⟨t1', u', t', e1', e2', hu', hp'⟩ := (der_app hρ').mp hz2
    obtain ⟨e3, e4⟩ := H.op_inj (e2.symm.trans e1')
    rw [← e3, ← e4] at hp'
    rw [← e4] at e2'
    exact ⟨t, u, t', e1, e2', hu, app_comp.mpr ⟨_, hp, hp'⟩⟩
  · rintro ⟨t, u, t', e1, e2, hu, hc⟩
    obtain ⟨z, hz1, hz2⟩ := app_comp.mp hc
    obtain ⟨t1, e⟩ := piso_mid hπ hz1
    rw [e] at hz1 hz2
    exact ⟨H.op t1 u, (der_app hρ).mpr ⟨t, u, t1, e1, rfl, hu, hz1⟩,
      (der_app hρ').mpr ⟨t1, u, t', rfl, e2, hu, hz2⟩⟩

theorem der_inv {π α β ρ : H.W} (hρ : H.IsDer π α β ρ) : H.IsDer (H.inv π) α β (H.inv ρ) := by
  refine isDer_of_app (isFun_inv_pairs ρ) fun v w => ?_
  rw [app_inv, der_app hρ]
  constructor
  · rintro ⟨t, u, t', e1, e2, hu, hp⟩
    exact ⟨t', u, t, e2, e1, hu, app_inv.mpr hp⟩
  · rintro ⟨t, u, t', e1, e2, hu, hp⟩
    exact ⟨t', u, t, e2, e1, hu, app_inv.mp hp⟩

/-- The action on pre-objects is functional. -/
theorem actRaw_fun {F α π x y y' : H.W} (h : H.ActRaw F α π x y) (h' : H.ActRaw F α π x y') :
    y = y' := by
  obtain ⟨β, D, D', e1, e2, hD⟩ := h
  obtain ⟨β2, D2, D2', e1', e2', hD'⟩ := h'
  obtain ⟨e3, e4⟩ := H.op_inj (e1.symm.trans e1')
  rw [e2, e2', ← e3]
  congr 1
  refine H.ext' fun z => ?_
  rw [hD z, hD' z, ← e3, ← e4]

end Host


/-! ## The invariants of a level, and the action on the lower levels -/

namespace Host

variable {H : Host}

namespace Tower

variable (T : Tower H)

theorem hdM : H.suc T.d ∈ T.M := T.hM.trans _ _ (H.suc_mem_om T.hd) T.hM.om_mem

theorem hdMp : H.suc T.d ∈ T.Mp := T.hMp.trans _ _ (H.suc_mem_om T.hd) T.hMp.om_mem

theorem sub_mem_Mp {x : H.W} (h : H.Sub x T.M) : x ∈ T.Mp := T.hMp.sub _ _ h T.hMMp

theorem M_sub_Mp {x : H.W} (h : x ∈ T.M) : x ∈ T.Mp := T.hMp.trans _ _ h T.hMMp

theorem proper_om {α : H.W} (hα : T.Proper α) : α ∈ H.om := by
  rcases H.mem_suc.mp hα.1 with h | h
  · exact (H.om_trans _ T.hd α h).1
  · rw [h]
    exact T.hd

theorem lower_suc {α γ : H.W} (hα : T.Proper α) (hγα : γ ∈ α) : γ ∈ H.suc T.d := by
  rcases H.mem_suc.mp hα.1 with h | h
  · exact H.mem_suc.mpr (Or.inl (H.om_mem_trans T.hd h hγα))
  · rw [h] at hγα
    exact H.mem_suc.mpr (Or.inl hγα)

theorem lower_proper {α γ : H.W} (hα : T.Proper α) (hγα : γ ∈ α) (h0 : γ ≠ H.emp) :
    T.Proper γ := ⟨T.lower_suc hα hγα, h0⟩

theorem emp_mem_proper {α : H.W} (hα : T.Proper α) : H.emp ∈ α :=
  (H.emp_mem_or (T.proper_om hα)).resolve_left hα.2

theorem mem_Gs {α π : H.W} (hα : T.Proper α) : π ∈ T.Gs α ↔ H.IsAut T.M T.d T.F α π := by
  rw [(T.spec hα).2.1]
  exact ⟨fun h => h.2, fun h => ⟨T.sub_mem_Mp (aut_sub T.hM T.hdM h.1), h⟩⟩

theorem Tp_sub {α x : H.W} (hα : T.Proper α) (h : x ∈ T.Tp α) : x ∈ T.Mp :=
  (((T.spec hα).2.2.1 x).mp h).1

theorem mem_Ts_emp {z : H.W} : z ∈ T.Ts H.emp ↔ H.IsAtom T.M z := by
  unfold Ts
  rw [ite_eq_left rfl]
  exact H.mem_atoms

theorem Ts_of_ne {β : H.W} (h : β ≠ H.emp) : T.Ts β = T.Tp β := by
  unfold Ts
  rw [ite_eq_right h]

/-- The invariants of the proper level `β`. -/
structure InvT (β : H.W) : Prop where
  act_tot : ∀ π x, π ∈ T.Gs β → x ∈ T.Tp β → ∃ y, y ∈ T.Tp β ∧ H.ActRaw T.F β π x y
  act_comp : ∀ π σ x y z, π ∈ T.Gs β → σ ∈ T.Gs β → x ∈ T.Tp β → H.ActRaw T.F β π x y →
    H.ActRaw T.F β σ y z → H.ActRaw T.F β (H.comp σ π) x z
  act_inv : ∀ π x y, π ∈ T.Gs β → x ∈ T.Tp β → H.ActRaw T.F β π x y →
    H.ActRaw T.F β (H.inv π) y x
  names : ∀ c, c ∈ T.Ns β → ∃ La, H.App T.Λ (H.suc β) La ∧ c ∈ La
  dec_tot : ∀ c S, H.Desc T.M T.d T.F (H.suc β) β c S → ∃ y, H.op c (H.op S y) ∈ T.Ds β
  dec_fun : ∀ c S y y', H.op c (H.op S y) ∈ T.Ds β → H.op c (H.op S y') ∈ T.Ds β → y = y'
  dec_mem : ∀ c S y, H.op c (H.op S y) ∈ T.Ds β →
    y ∈ T.Tp β ∧ H.Desc T.M T.d T.F (H.suc β) β c S
  dec_surj : ∀ x, x ∈ T.Tp β → ∃ c S, H.op c (H.op S x) ∈ T.Ds β
  dec_equi : ∀ π c S S' y y', π ∈ T.Gs β → H.op c (H.op S y) ∈ T.Ds β →
    H.Desc T.M T.d T.F (H.suc β) β c S' → (∀ j v, H.App S j v → ∃ w, H.App S' j w ∧ H.App π v w) →
    H.ActRaw T.F β π y y' → H.op c (H.op S' y') ∈ T.Ds β
  dec_supp : ∀ c S y, H.op c (H.op S y) ∈ T.Ds β → H.SuppTup T.F (T.Gs β) β S y
  tp_mem : β ∈ T.d → T.Tp β ∈ T.Mp
  lit : ∀ b l, H.IsLabel T.M b → H.IsLit T.M b l → l ∈ T.Tp β

theorem inA_act {α γ ρ z z' : H.W} (h : H.InA T.F α γ ρ z z') :
    T.Proper γ ∧ ρ ∈ T.Gs γ ∧ z ∈ T.Tp γ ∧ H.ActRaw T.F γ ρ z z' := by
  obtain ⟨-, τ, G, A, N, D, hr, hq⟩ := h
  have hγ := T.rec_proper hr
  rw [(T.rec_unique hγ hr).2.2.1] at hq
  obtain ⟨-, π1, x1, y1, e1, hG, hx, hact⟩ := ((T.spec hγ).2.2.2.1 _).mp hq
  obtain ⟨a1, a2⟩ := H.op_inj e1
  obtain ⟨a3, a4⟩ := H.op_inj a2
  rw [a1, a3, a4]
  exact ⟨hγ, hG, hx, hact⟩

theorem tok_atom_top {α z : H.W} (hα : T.Proper α) (hz : H.IsAtom T.M z) :
    H.IsTok T.M T.d α (H.op z (H.sg α)) :=
  ⟨z, H.sg α, rfl, fun x hx => by rw [H.mem_sg.mp hx]; exact hα,
    Or.inr ⟨H.mem_sg.mpr rfl, fun x hx => H.mem_suc.mpr (Or.inr (H.mem_sg.mp hx))⟩, Or.inl hz⟩

section low

variable {α γ π σ ρ z z' z'' : H.W}

theorem low_fun (hπ : H.IsFun π) (h : H.ActLow T.F α π γ z z')
    (h' : H.ActLow T.F α π γ z z'') : z' = z'' := by
  rcases h with ⟨e, h⟩ | ⟨h0, ρ, hρ, hA⟩
  · rcases h' with ⟨-, h'⟩ | ⟨h0', -⟩
    · exact (H.op_inj (hπ.2 _ _ _ h h')).1
    · exact (h0' e).elim
  · rcases h' with ⟨e, -⟩ | ⟨-, ρ', hρ', hA'⟩
    · exact (h0 e).elim
    · rw [der_unique hρ' hρ] at hA'
      exact actRaw_fun (T.inA_act hA).2.2.2 (T.inA_act hA').2.2.2

theorem low_proper (hα : T.Proper α) (hIγ : T.InvT γ) (hγα : γ ∈ α) (hγ0 : γ ≠ H.emp)
    (hπ : H.IsAut T.M T.d T.F α π) (hρ : H.IsDer π α γ ρ) :
    H.ActLow T.F α π γ z z' ↔ z ∈ T.Tp γ ∧ H.ActRaw T.F γ ρ z z' := by
  have hγ := T.lower_proper hα hγα hγ0
  have hρG : ρ ∈ T.Gs γ := (T.mem_Gs hγ).mpr (der_aut (T.proper_om hα) hα.1 hγα hγ0 hπ hρ)
  constructor
  · rintro (⟨e, -⟩ | ⟨-, ρ', hρ', hA⟩)
    · exact (hγ0 e).elim
    · rw [der_unique hρ' hρ] at hA
      exact ⟨(T.inA_act hA).2.2.1, (T.inA_act hA).2.2.2⟩
  · rintro ⟨hz, hact⟩
    refine Or.inr ⟨hγ0, ρ, hρ, (T.inA_iff hγ hγα).mpr (((T.spec hγ).2.2.2.1 _).mpr
      ⟨?_, ρ, z, z', rfl, hρG, hz, hact⟩)⟩
    obtain ⟨y, hy, hact'⟩ := hIγ.act_tot ρ z hρG hz
    rw [actRaw_fun hact hact']
    exact T.hMp.op_mem (((T.spec hγ).2.1 ρ).mp hρG).1
      (T.hMp.op_mem (T.Tp_sub hγ hz) (T.Tp_sub hγ hy))

variable (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

theorem low_tot (hπ : H.IsAut T.M T.d T.F α π) (hγα : γ ∈ α) (hz : z ∈ T.Ts γ) :
    ∃ z', z' ∈ T.Ts γ ∧ H.ActLow T.F α π γ z z' := by
  by_cases hγ0 : γ = H.emp
  · subst hγ0
    have hza := T.mem_Ts_emp.mp hz
    obtain ⟨w, hw⟩ := hπ.2.1 _ (T.tok_atom_top hα hza)
    obtain ⟨z', e⟩ := piso_mid hπ.1 hw
    rw [e] at hw
    refine ⟨z', T.mem_Ts_emp.mpr ⟨?_, (hπ.1.2.2.2.1 _ _ _ _ hw).2.mp hza.2⟩, Or.inl ⟨rfl, hw⟩⟩
    exact (T.hM.of_op_mem (tok_mem T.hM T.hdM (hπ.1.2.1 _ _ hw).2)).1
  · have hγ := T.lower_proper hα hγα hγ0
    obtain ⟨ρ, hρ, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hπ.1) α γ
    rw [T.Ts_of_ne hγ0] at hz ⊢
    have hρG : ρ ∈ T.Gs γ := (T.mem_Gs hγ).mpr (der_aut (T.proper_om hα) hα.1 hγα hγ0 hπ hρ)
    obtain ⟨y, hy, hact⟩ := (hI γ hγα hγ).act_tot ρ z hρG hz
    exact ⟨y, hy, (T.low_proper hα (hI γ hγα hγ) hγα hγ0 hπ hρ).mpr ⟨hz, hact⟩⟩

theorem low_mem (hπ : H.IsAut T.M T.d T.F α π) (hγα : γ ∈ α) (hz : z ∈ T.Ts γ)
    (h : H.ActLow T.F α π γ z z') : z' ∈ T.Ts γ := by
  obtain ⟨y, hy, hact⟩ := T.low_tot hα hI hπ hγα hz
  rw [T.low_fun hπ.1.1 h hact]
  exact hy

theorem low_inv (hπ : H.IsAut T.M T.d T.F α π) (hγα : γ ∈ α) (hz : z ∈ T.Ts γ)
    (h : H.ActLow T.F α π γ z z') : H.ActLow T.F α (H.inv π) γ z' z := by
  have hz' := T.low_mem hα hI hπ hγα hz h
  by_cases hγ0 : γ = H.emp
  · subst hγ0
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩
    · exact Or.inl ⟨rfl, app_inv.mpr h⟩
    · exact (h0 rfl).elim
  · have hγ := T.lower_proper hα hγα hγ0
    obtain ⟨ρ, hρ, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hπ.1) α γ
    rw [T.Ts_of_ne hγ0] at hz hz'
    have hρG : ρ ∈ T.Gs γ := (T.mem_Gs hγ).mpr (der_aut (T.proper_om hα) hα.1 hγα hγ0 hπ hρ)
    obtain ⟨-, hact⟩ := (T.low_proper hα (hI γ hγα hγ) hγα hγ0 hπ hρ).mp h
    exact (T.low_proper hα (hI γ hγα hγ) hγα hγ0 (isAut_inv hπ) (der_inv hρ)).mpr
      ⟨hz', (hI γ hγα hγ).act_inv ρ z z' hρG hz hact⟩

theorem low_comp (hπ : H.IsAut T.M T.d T.F α π) (hσ : H.IsAut T.M T.d T.F α σ) (hγα : γ ∈ α)
    (hz : z ∈ T.Ts γ) (h : H.ActLow T.F α π γ z z') (h' : H.ActLow T.F α σ γ z' z'') :
    H.ActLow T.F α (H.comp σ π) γ z z'' := by
  by_cases hγ0 : γ = H.emp
  · subst hγ0
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩
    · rcases h' with ⟨-, h'⟩ | ⟨h0', -⟩
      · exact Or.inl ⟨rfl, app_comp.mpr ⟨_, h, h'⟩⟩
      · exact (h0' rfl).elim
    · exact (h0 rfl).elim
  · have hγ := T.lower_proper hα hγα hγ0
    have hz' := T.low_mem hα hI hπ hγα hz h
    obtain ⟨ρ, hρ, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hπ.1) α γ
    obtain ⟨ρ', hρ', -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hσ.1) α γ
    rw [T.Ts_of_ne hγ0] at hz hz'
    have hρG : ρ ∈ T.Gs γ := (T.mem_Gs hγ).mpr (der_aut (T.proper_om hα) hα.1 hγα hγ0 hπ hρ)
    have hρG' : ρ' ∈ T.Gs γ := (T.mem_Gs hγ).mpr (der_aut (T.proper_om hα) hα.1 hγα hγ0 hσ hρ')
    obtain ⟨-, hact⟩ := (T.low_proper hα (hI γ hγα hγ) hγα hγ0 hπ hρ).mp h
    obtain ⟨-, hact'⟩ := (T.low_proper hα (hI γ hγα hγ) hγα hγ0 hσ hρ').mp h'
    exact (T.low_proper hα (hI γ hγα hγ) hγα hγ0 (isAut_comp hπ hσ) (der_comp hπ.1 hρ hρ')).mpr
      ⟨hz, (hI γ hγα hγ).act_comp ρ ρ' z z' z'' hρG hρG' hz hact hact'⟩

end low

/-- A pre-object of the stage `α`: a set of objects of one lower level, tagged by the level. -/
def Pre (α x : H.W) : Prop := ∃ γ D, x = H.op γ D ∧ γ ∈ α ∧ ∀ z, z ∈ D → z ∈ T.Ts γ

section raw

variable {α π σ x y z : H.W} (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

theorem raw_tot (hπ : H.IsAut T.M T.d T.F α π) (hx : T.Pre α x) :
    ∃ y, T.Pre α y ∧ H.ActRaw T.F α π x y := by
  obtain ⟨γ, D, e, hγα, hD⟩ := hx
  obtain ⟨D', hD'⟩ := H.sep' (T.Ts γ) (fun z' => ∃ z, z ∈ D ∧ H.ActLow T.F α π γ z z') (by hdef)
  refine ⟨H.op γ D', ⟨γ, D', rfl, hγα, fun z hz => ((hD' z).mp hz).1⟩, γ, D, D', e, rfl,
    fun z' => ⟨fun h => ((hD' z').mp h).2, fun h => (hD' z').mpr ⟨?_, h⟩⟩⟩
  obtain ⟨z, hz, hact⟩ := h
  exact T.low_mem hα hI hπ hγα (hD z hz) hact

theorem raw_pre (hπ : H.IsAut T.M T.d T.F α π) (hx : T.Pre α x) (h : H.ActRaw T.F α π x y) :
    T.Pre α y := by
  obtain ⟨y', hy', hact⟩ := T.raw_tot hα hI hπ hx
  rw [actRaw_fun h hact]
  exact hy'

theorem raw_inv (hπ : H.IsAut T.M T.d T.F α π) (hx : T.Pre α x) (h : H.ActRaw T.F α π x y) :
    H.ActRaw T.F α (H.inv π) y x := by
  obtain ⟨γ, D, e, hγα, hD⟩ := hx
  obtain ⟨γ', D0, D', e1, e2, hD'⟩ := h
  obtain ⟨e3, e4⟩ := H.op_inj (e.symm.trans e1)
  rw [← e3] at e2 hD'
  rw [← e4] at hD'
  refine ⟨γ, D', D, e2, e, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨z', -, hact⟩ := T.low_tot hα hI hπ hγα (hD z hz)
    exact ⟨z', (hD' z').mpr ⟨z, hz, hact⟩, T.low_inv hα hI hπ hγα (hD z hz) hact⟩
  · obtain ⟨z', hz', hact⟩ := hz
    obtain ⟨z0, hz0, hact0⟩ := (hD' z').mp hz'
    rw [T.low_fun (isAut_inv hπ).1.1 hact (T.low_inv hα hI hπ hγα (hD z0 hz0) hact0)]
    exact hz0

theorem raw_comp (hπ : H.IsAut T.M T.d T.F α π) (hσ : H.IsAut T.M T.d T.F α σ) (hx : T.Pre α x)
    (h : H.ActRaw T.F α π x y) (h' : H.ActRaw T.F α σ y z) :
    H.ActRaw T.F α (H.comp σ π) x z := by
  obtain ⟨γ, D, e, hγα, hD⟩ := hx
  obtain ⟨γ', D0, D', e1, e2, hD'⟩ := h
  obtain ⟨e3, e4⟩ := H.op_inj (e.symm.trans e1)
  rw [← e3] at e2 hD'
  rw [← e4] at hD'
  obtain ⟨γ'', D1, D'', e1', e2', hD''⟩ := h'
  obtain ⟨e3', e4'⟩ := H.op_inj (e2.symm.trans e1')
  rw [← e3'] at e2' hD''
  rw [← e4'] at hD''
  refine ⟨γ, D, D'', e, e2', fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · obtain ⟨z', hz', hact'⟩ := (hD'' w).mp hw
    obtain ⟨z0, hz0, hact0⟩ := (hD' z').mp hz'
    exact ⟨z0, hz0, T.low_comp hα hI hπ hσ hγα (hD z0 hz0) hact0 hact'⟩
  · obtain ⟨z0, hz0, hact⟩ := hw
    obtain ⟨z', hz', hact0⟩ := T.low_tot hα hI hπ hγα (hD z0 hz0)
    obtain ⟨w', -, hact'⟩ := T.low_tot hα hI hσ hγα hz'
    rw [T.low_fun (isAut_comp hπ hσ).1.1 hact
      (T.low_comp hα hI hπ hσ hγα (hD z0 hz0) hact0 hact')]
    exact (hD'' w').mpr ⟨z', (hD' z').mpr ⟨z0, hz0, hact0⟩, hact'⟩

end raw

/-- The objects of a stage are pre-objects. -/
theorem obj_pre {α x : H.W} (hα : T.Proper α) (hx : x ∈ T.Tp α) : T.Pre α x := by
  obtain ⟨-, β, D, e, h | h, -⟩ := ((T.spec hα).2.2.1 x).mp hx
  · refine ⟨β, D, e, ?_, fun z hz => ?_⟩
    · rw [h.2]
      exact T.emp_mem_proper hα
    · rw [h.1] at hz
      exact (H.not_mem_emp z hz).elim
  · exact ⟨β, D, e, h.2.1, fun z hz => (T.inT_iff (T.lower_suc hα h.2.1) h.2.1).mp (h.2.2.1 z hz)⟩

end Tower

end Host


/-! ## Literal litters, images of finite sets, supports under conjugation -/

namespace Host

variable {H : Host}

theorem lit_ex (M b : H.W) : ∃ l, H.IsLit M b l := by
  obtain ⟨L, hL⟩ := H.sep' (H.atoms M) (fun a => H.Adj a b) (by hdef)
  exact ⟨H.op H.emp L, L, rfl, fun a => (hL a).trans (and_congr H.mem_atoms Iff.rfl)⟩

theorem lit_unique {M b l l' : H.W} (h : H.IsLit M b l) (h' : H.IsLit M b l') : l = l' := by
  obtain ⟨L, e, hL⟩ := h
  obtain ⟨L', e', hL'⟩ := h'
  rw [e, e', H.ext' fun a => (hL a).trans (hL' a).symm]

/-- Distinct labels have distinct literal litters. -/
theorem lit_inj {M b b' l : H.W} (hM : H.Closed M) (hb : b ∈ M) (hb' : b' ∈ M)
    (h : H.IsLit M b l) (h' : H.IsLit M b' l) : b = b' := by
  obtain ⟨L, e, hL⟩ := h
  obtain ⟨L', e', hL'⟩ := h'
  have eL : L = L' := (H.op_inj (e.symm.trans e')).2
  refine hM.label_ext hb hb' fun a ha => ?_
  have h1 := hL a
  have h2 := hL' a
  rw [eL] at h1
  exact ⟨fun hadj => (h2.mp (h1.mpr ⟨ha, hadj⟩)).2, fun hadj => (h1.mp (h2.mpr ⟨ha, hadj⟩)).2⟩

/-- The image of a finite set under a function is finite. -/
theorem fin_image {Sp π : H.W} (hSp : H.Fin Sp) (hπ : H.IsFun π)
    (htot : ∀ v, v ∈ Sp → ∃ w, H.App π v w) :
    ∃ Sp', H.Fin Sp' ∧ ∀ w, w ∈ Sp' ↔ ∃ v, v ∈ Sp ∧ H.App π v w := by
  obtain ⟨n, f, hn, hf, hSp⟩ := hSp
  refine ⟨H.ran (H.comp π f), ⟨n, H.comp π f, hn, ⟨⟨comp_pairs π f, fun a b b' h h' => ?_⟩,
    fun i => ?_⟩, fun z => H.mem_ran⟩, fun w => ?_⟩
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    obtain ⟨z', hz1', hz2'⟩ := app_comp.mp h'
    rw [hf.1.2 _ _ _ hz1 hz1'] at hz2
    exact hπ.2 _ _ _ hz2 hz2'
  · rw [hf.2 i]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨w, hw⟩ := htot z ((hSp z).mpr ⟨i, hz⟩)
      exact ⟨w, app_comp.mpr ⟨z, hz, hw⟩⟩
    · rintro ⟨w, hw⟩
      obtain ⟨z, hz, -⟩ := app_comp.mp hw
      exact ⟨z, hz⟩
  · rw [H.mem_ran]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨z, hz1, hz2⟩ := app_comp.mp hi
      exact ⟨z, (hSp z).mpr ⟨i, hz1⟩, hz2⟩
    · rintro ⟨v, hv, hvw⟩
      obtain ⟨i, hi⟩ := (hSp v).mp hv
      exact ⟨i, app_comp.mpr ⟨v, hi, hvw⟩⟩

namespace Tower

variable (T : Tower H)

/-- Access to the decoding at a lower level. -/
theorem inD_iff {α β c S y : H.W} (hβ : T.Proper β) (hβα : β ∈ α) :
    H.InD T.M T.d T.F α β c S y ↔ H.op c (H.op S y) ∈ T.Ds β := by
  unfold InD
  constructor
  · rintro (⟨e, -⟩ | ⟨-, -, τ, G, A, N, D, hr, hq⟩)
    · exact (hβ.2 e).elim
    · rw [← (T.rec_unique hβ hr).2.2.2.2]
      exact hq
  · intro hq
    exact Or.inr ⟨hβ.2, hβα, _, _, _, _, _, (T.spec hβ).1, hq⟩

theorem tok_label_top {α b : H.W} (hα : T.Proper α) (hb : H.IsLabel T.M b) :
    H.IsTok T.M T.d α (H.op b (H.sg α)) :=
  ⟨b, H.sg α, rfl, fun x hx => by rw [H.mem_sg.mp hx]; exact hα,
    Or.inr ⟨H.mem_sg.mpr rfl, fun x hx => H.mem_suc.mpr (Or.inr (H.mem_sg.mp hx))⟩,
    Or.inr ⟨hb, fun h0 => H.not_mem_emp α (h0 ▸ H.mem_sg.mpr rfl)⟩⟩

/-- An automorphism acts on the literal litters through its action on the labels. -/
theorem lit_act {α π b b' l l' : H.W} (hα : T.Proper α) (hπ : H.IsAut T.M T.d T.F α π)
    (hb : H.IsLabel T.M b) (hbb : H.App π (H.op b (H.sg α)) (H.op b' (H.sg α)))
    (hl : H.IsLit T.M b l) (hl' : H.IsLit T.M b' l') : H.ActRaw T.F α π l l' := by
  obtain ⟨L, e, hL⟩ := hl
  obtain ⟨L', e', hL'⟩ := hl'
  refine ⟨H.emp, L, L', e, e', fun z' => ?_⟩
  rw [hL']
  constructor
  · rintro ⟨hz', hadj⟩
    obtain ⟨v, hv⟩ := hπ.2.2 _ (T.tok_atom_top hα hz')
    obtain ⟨z, ev⟩ := piso_mid' hπ.1 hv
    rw [ev] at hv
    have hz : H.IsAtom T.M z :=
      ⟨(T.hM.of_op_mem (tok_mem T.hM T.hdM (hπ.1.2.1 _ _ hv).1)).1,
        (hπ.1.2.2.2.1 _ _ _ _ hv).2.mpr hz'.2⟩
    exact ⟨z, (hL z).mpr ⟨hz, (hπ.1.2.2.2.2.1 z b _ z' b' hv hbb hz.2 hb.2).mpr hadj⟩,
      Or.inl ⟨rfl, hv⟩⟩
  · rintro ⟨z, hz, (⟨-, h⟩ | ⟨h0, -⟩)⟩
    · obtain ⟨hza, hadj⟩ := (hL z).mp hz
      exact ⟨⟨(T.hM.of_op_mem (tok_mem T.hM T.hdM (hπ.1.2.1 _ _ h).2)).1,
        (hπ.1.2.2.2.1 _ _ _ _ h).2.mp hza.2⟩,
        (hπ.1.2.2.2.2.1 z b _ z' b' h hbb hza.2 hb.2).mp hadj⟩
    · exact (h0 rfl).elim

/-- The literal litters are objects of every proper level. -/
theorem lit_mem {α b l : H.W} (hα : T.Proper α) (hb : H.IsLabel T.M b) (hl : H.IsLit T.M b l) :
    l ∈ T.Tp α := by
  obtain ⟨L, e, hL⟩ := id hl
  have hLM : H.Sub L T.M := fun a ha => ((hL a).mp ha).1.1
  have hL0 : L ≠ H.emp := by
    obtain ⟨a, ha, hadj, -, -⟩ := T.hM.exists_atom (P := H.sg b) (N := H.emp) (Z := H.emp)
      (T.hM.sg_mem hb.1) T.hM.emp_mem T.hM.emp_mem (fun x _ hx => H.not_mem_emp x hx)
    exact fun h0 => H.not_mem_emp a (h0 ▸ (hL a).mpr ⟨ha, hadj b (H.mem_sg.mpr rfl)⟩)
  refine ((T.spec hα).2.2.1 l).mpr ⟨?_, H.emp, L, e, Or.inr ⟨hL0, T.emp_mem_proper hα,
    fun z hz => Or.inl ⟨rfl, ((hL z).mp hz).1⟩, ?_⟩, H.sg (H.op b (H.sg α)), H.fin_sg _,
    fun v hv => by rw [H.mem_sg.mp hv]; exact T.tok_label_top hα hb, fun π hπ hfix => ?_⟩
  · rw [e]
    exact T.hMp.op_mem T.hMp.emp_mem (T.sub_mem_Mp hLM)
  · exact ⟨H.emp, H.ins H.emp H.emp (H.op H.emp L), H.sg H.emp, H.emp_mem_om,
      H.funOn_ins H.funOn_emp, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩),
      fun i hi => (H.not_mem_emp i hi).elim,
      ⟨H.emp, L, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩), fun ⟨γ, X, hinv⟩ => hinv.2.2.1 rfl⟩,
      H.mem_sg.mpr rfl, H.mem_sg.mpr rfl, fun i hi => (H.not_mem_emp i hi).elim⟩
  · exact T.lit_act hα ((T.mem_Gs hα).mp hπ) hb (hfix _ (H.mem_sg.mpr rfl)) hl hl

/-- The image of a support under an automorphism supports the image of the object. -/
theorem supp_conj {α π x y Sp Sp' : H.W} (hα : T.Proper α)
    (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ) (hπ : H.IsAut T.M T.d T.F α π) (hx : T.Pre α x)
    (h : H.ActRaw T.F α π x y) (hSp : H.SuppSet T.F (T.Gs α) α Sp x)
    (hSp' : ∀ v, v ∈ Sp → ∃ w, w ∈ Sp' ∧ H.App π v w) : H.SuppSet T.F (T.Gs α) α Sp' y := by
  intro σ hσG hfix
  have hσ := (T.mem_Gs hα).mp hσG
  have hy := T.raw_pre hα hI hπ hx h
  obtain ⟨y', hy', hact'⟩ := T.raw_tot hα hI hσ hy
  obtain ⟨x', -, hact''⟩ := T.raw_tot hα hI (isAut_inv hπ) hy'
  have hκ := isAut_comp (isAut_comp hπ hσ) (isAut_inv hπ)
  have h1 := T.raw_comp hα hI (isAut_comp hπ hσ) (isAut_inv hπ) hx
    (T.raw_comp hα hI hπ hσ hx h hact') hact''
  have h2 : H.ActRaw T.F α (H.comp (H.inv π) (H.comp σ π)) x x :=
    hSp _ ((T.mem_Gs hα).mpr hκ) (fun v hv => by
      obtain ⟨w, hw, hvw⟩ := hSp' v hv
      exact app_comp.mpr ⟨w, app_comp.mpr ⟨w, hvw, hfix w hw⟩, app_inv.mpr hvw⟩)
  rw [actRaw_fun h1 h2] at hact''
  have h3 := T.raw_inv hα hI (isAut_inv hπ) hy' hact''
  rw [inv_inv hπ.1.1.1] at h3
  have e : y = y' := actRaw_fun h h3
  rw [← e] at hact'
  exact hact'

end Tower

end Host


/-! ## Fibre transport: the action commutes with the alternate extensions -/

namespace Host

variable {H : Host}

theorem emp_bun (a : H.W) : H.bun H.emp a = a :=
  H.ext' fun z => by
    rw [H.mem_bun]
    exact ⟨fun h => h.elim (fun h => (H.not_mem_emp z h).elim) id, Or.inr⟩

namespace Tower

variable (T : Tower H)

theorem lower_mem_d {α γ : H.W} (hα : T.Proper α) (hγα : γ ∈ α) : γ ∈ T.d := by
  rcases H.mem_suc.mp hα.1 with h | h
  · exact H.om_mem_trans T.hd h hγα
  · rw [h] at hγα
    exact hγα

section stage

variable {α : H.W} (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

theorem pre_mem_Mp {y : H.W} (hy : T.Pre α y) : y ∈ T.Mp := by
  obtain ⟨γ, D, e, hγα, hD⟩ := hy
  rw [e]
  refine T.hMp.op_mem (T.hMp.trans _ _ (T.lower_suc hα hγα) T.hdMp) ?_
  by_cases hγ0 : γ = H.emp
  · refine T.sub_mem_Mp fun z hz => ?_
    have := hD z hz
    rw [hγ0] at this
    exact (T.mem_Ts_emp.mp this).1
  · have hγ := T.lower_proper hα hγα hγ0
    refine T.hMp.sub _ _ (fun z hz => ?_) ((hI γ hγα hγ).tp_mem (T.lower_mem_d hα hγα))
    have := hD z hz
    rw [T.Ts_of_ne hγ0] at this
    exact this

/-- **One label of a fibre.** An automorphism sends a label of the fibre of a descriptor to a
label of the fibre of the image descriptor; the decoded objects and the literal litters
correspond. -/
theorem fibre_step {γ δ π c S X' η x l : H.W} (hπ : H.IsAut T.M T.d T.F α π)
    (hγα : γ ∈ α) (hδα : δ ∈ α) (hδ0 : δ ≠ H.emp) (hγδ : γ ≠ δ)
    (hdesc : H.Desc T.M T.d T.F α γ c S) (hdec : H.InD T.M T.d T.F α γ c S x)
    (hbM : H.label (H.op γ δ) (H.op c S) X' η ∈ T.M)
    (hl : H.IsLit T.M (H.label (H.op γ δ) (H.op c S) X' η) l) :
    ∃ S' X'' η'' x' l', H.Desc T.M T.d T.F α γ c S' ∧ H.InD T.M T.d T.F α γ c S' x' ∧
      H.label (H.op γ δ) (H.op c S') X'' η'' ∈ T.M ∧
      H.IsLit T.M (H.label (H.op γ δ) (H.op c S') X'' η'') l' ∧
      H.ActLow T.F α π γ x x' ∧ H.ActLow T.F α π δ l l' := by
  have hαo := T.proper_om hα
  have hδ := T.lower_proper hα hδα hδ0
  obtain ⟨b, hb⟩ : ∃ b, b = H.label (H.op γ δ) (H.op c S) X' η := ⟨_, rfl⟩
  rw [← hb] at hbM hl
  have hbl : H.IsLabel T.M b := ⟨hbM, _, _, _, _, hb⟩
  have hδp : δ ∈ H.bun (H.sg δ) (H.sg α) := H.mem_bun.mpr (Or.inl (H.mem_sg.mpr rfl))
  have hαp : α ∈ H.bun (H.sg δ) (H.sg α) := H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl))
  have hαδ : α ≠ δ := fun e => H.mem_irrefl α (by rw [← e] at hδα; exact hδα)
  have htok : H.IsTok T.M T.d α (H.op b (H.bun (H.sg δ) (H.sg α))) := by
    refine ⟨b, _, rfl, fun x hx => ?_, Or.inr ⟨hαp, fun x hx => ?_⟩,
      Or.inr ⟨hbl, fun h0 => H.not_mem_emp α (h0 ▸ hαp)⟩⟩
    · rcases H.mem_bun.mp hx with hx | hx
      · rw [H.mem_sg.mp hx]
        exact hδ
      · rw [H.mem_sg.mp hx]
        exact hα
    · rcases H.mem_bun.mp hx with hx | hx
      · rw [H.mem_sg.mp hx]
        exact H.mem_suc.mpr (Or.inl hδα)
      · exact H.mem_suc.mpr (Or.inr (H.mem_sg.mp hx))
  have hcol : H.Col T.M T.d T.F α (H.op b (H.bun (H.sg δ) (H.sg α))) γ δ c S (H.sg α) := by
    refine col_iff.mpr ⟨⟨X', η, hb⟩, ⟨hδp, fun x hx => ?_⟩, fun x => ?_,
      fun h0 => H.not_mem_emp α (h0 ▸ H.mem_sg.mpr rfl), hγδ, fun x hx => ?_, hdesc⟩
    · rcases H.mem_bun.mp hx with hx | hx
      · exact H.mem_suc.mpr (Or.inr (H.mem_sg.mp hx).symm)
      · rw [H.mem_sg.mp hx]
        exact H.mem_suc.mpr (Or.inl hδα)
    · constructor
      · intro hx
        rw [H.mem_sg.mp hx]
        exact ⟨hαp, hαδ⟩
      · rintro ⟨hx, hne⟩
        rcases H.mem_bun.mp hx with hx | hx
        · exact (hne (H.mem_sg.mp hx)).elim
        · exact hx
    · rw [H.mem_sg.mp hx]
      exact hγα
  obtain ⟨w, hw⟩ := hπ.2.1 _ htok
  obtain ⟨b', ew⟩ := piso_mid hπ.1 hw
  rw [ew] at hw
  obtain ⟨S', hS', hco⟩ := hπ.1.2.2.2.2.2.1 _ _ γ δ c S (H.sg α) hw hcol
  obtain ⟨⟨X'', η'', eb'⟩, -, -, -, -, -, hdesc'⟩ := col_iff.mp hS'
  have hb'M : b' ∈ T.M := (T.hM.of_op_mem (tok_mem T.hM T.hdM (hπ.1.2.1 _ _ hw).2)).1
  obtain ⟨l', hl'⟩ := H.lit_ex T.M b'
  have hlit : H.ActLow T.F α π δ l l' := by
    obtain ⟨ρ, hρ, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hπ.1) α δ
    have hρA := der_aut hαo hα.1 hδα hδ0 hπ hρ
    exact (T.low_proper hα (hI δ hδα hδ) hδα hδ0 hπ hρ).mpr ⟨T.lit_mem hδ hbl hl,
      T.lit_act hδ hρA hbl ((der_app hρ).mpr ⟨b, H.sg δ, b', rfl, rfl,
        Or.inr ⟨H.mem_sg.mpr rfl, fun x hx => H.mem_suc.mpr (Or.inr (H.mem_sg.mp hx))⟩, hw⟩)
        hl hl'⟩
  rw [eb'] at hb'M hl'
  by_cases hγ0 : γ = H.emp
  · rcases hdec with ⟨-, -, k, i, ec, hSi⟩ | ⟨h0, -⟩
    · obtain ⟨x', hx', hπx⟩ := hco i x H.emp hSi
      rw [emp_bun] at hπx
      exact ⟨S', X'', η'', x', l', hdesc', Or.inl ⟨hγ0, hdesc', k, i, ec, hx'⟩, hb'M, hl',
        Or.inl ⟨hγ0, hπx⟩, hlit⟩
    · exact (h0 hγ0).elim
  · have hγ := T.lower_proper hα hγα hγ0
    have hq := (T.inD_iff hγ hγα).mp hdec
    obtain ⟨ρ, hρ, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hπ.1) α γ
    have hρG : ρ ∈ T.Gs γ := (T.mem_Gs hγ).mpr (der_aut hαo hα.1 hγα hγ0 hπ hρ)
    have hxT := ((hI γ hγα hγ).dec_mem c S x hq).1
    obtain ⟨x', hx'T, hact⟩ := (hI γ hγα hγ).act_tot ρ x hρG hxT
    have hsuc : γ ∈ H.suc γ := H.mem_suc.mpr (Or.inr rfl)
    have hq' := (hI γ hγα hγ).dec_equi ρ c S S' x x' hρG hq
      ((desc_stage (β := H.suc γ) hsuc hγα).mpr hdesc') (fun j v hj => by
        obtain ⟨t, u, ev, -, hty, -⟩ := desc_tok hdesc hj
        rw [ev] at hj ⊢
        obtain ⟨t', ht', hπt⟩ := hco j t u hj
        exact ⟨_, ht', (der_app hρ).mpr ⟨t, u, t', rfl, rfl, hty, hπt⟩⟩) hact
    exact ⟨S', X'', η'', x', l', hdesc', (T.inD_iff hγ hγα).mpr hq', hb'M, hl',
      (T.low_proper hα (hI γ hγα hγ) hγα hγ0 hπ hρ).mpr ⟨hxT, hact⟩, hlit⟩

/-- **Fibre transport.** The alternate extension of the image is the image of the alternate
extension. -/
theorem alt_transport {γ δ π X Y X₂ Y₂ : H.W} (hπ : H.IsAut T.M T.d T.F α π)
    (hγα : γ ∈ α) (hδα : δ ∈ α) (hδ0 : δ ≠ H.emp) (hγδ : γ ≠ δ)
    (hX : ∀ z, z ∈ X → z ∈ T.Ts γ) (hY : H.IsAlt T.M T.d T.F α γ δ X Y)
    (hX₂ : ∀ z', z' ∈ X₂ ↔ ∃ z, z ∈ X ∧ H.ActLow T.F α π γ z z')
    (hY₂ : ∀ l', l' ∈ Y₂ ↔ ∃ l, l ∈ Y ∧ H.ActLow T.F α π δ l l') :
    H.IsAlt T.M T.d T.F α γ δ X₂ Y₂ := by
  have hδ := T.lower_proper hα hδα hδ0
  intro l'
  constructor
  · intro hl'
    obtain ⟨l, hl, hact⟩ := (hY₂ l').mp hl'
    obtain ⟨c, S, X', η, x, hdesc, hdec, hx, hbM, hlit⟩ := (hY l).mp hl
    obtain ⟨S', X'', η'', x', l'', hdesc', hdec', hb'M, hlit', hax, hal⟩ :=
      T.fibre_step hα hI hπ hγα hδα hδ0 hγδ hdesc hdec hbM hlit
    rw [T.low_fun hπ.1.1 hact hal]
    exact ⟨c, S', X'', η'', x', hdesc', hdec', (hX₂ x').mpr ⟨x, hx, hax⟩, hb'M, hlit'⟩
  · rintro ⟨c, S, X', η, x₂, hdesc, hdec, hx₂, hbM, hlit⟩
    obtain ⟨x₀, hx₀, hact₀⟩ := (hX₂ x₂).mp hx₂
    obtain ⟨S₀, X₀, η₀, x₀', l₀, hdesc₀, hdec₀, hb₀M, hlit₀, hax, hal⟩ :=
      T.fibre_step hα hI (isAut_inv hπ) hγα hδα hδ0 hγδ hdesc hdec hbM hlit
    have e : x₀' = x₀ :=
      T.low_fun (isAut_inv hπ).1.1 hax (T.low_inv hα hI hπ hγα (hX x₀ hx₀) hact₀)
    rw [e] at hdec₀
    refine (hY₂ l').mpr ⟨l₀, (hY l₀).mpr ⟨c, S₀, X₀, η₀, x₀, hdesc₀, hdec₀, hx₀, hb₀M, hlit₀⟩, ?_⟩
    have hl'T : l' ∈ T.Ts δ := by
      rw [T.Ts_of_ne hδ0]
      exact T.lit_mem hδ ⟨hbM, _, _, _, _, rfl⟩ hlit
    have h3 := T.low_inv hα hI (isAut_inv hπ) hδα hl'T hal
    rw [inv_inv hπ.1.1.1] at h3
    exact h3

omit hI in
theorem pre_of_inv {γ δ X Y : H.W} (hinv : H.IsInv T.M T.d T.F α δ Y γ X) :
    T.Pre α (H.op γ X) :=
  ⟨γ, X, rfl, hinv.1, fun z hz =>
    (T.inT_iff (T.lower_suc hα hinv.1) hinv.1).mp (hinv.2.2.2.2.2.1 z hz)⟩

/-- The partial inverse commutes with the action. -/
theorem inv_transport {γ δ π X Y x y : H.W} (hπ : H.IsAut T.M T.d T.F α π)
    (hinv : H.IsInv T.M T.d T.F α δ Y γ X)
    (hy : H.ActRaw T.F α π (H.op δ Y) y) (hx : H.ActRaw T.F α π (H.op γ X) x) :
    ∃ Y₂ X₂, y = H.op δ Y₂ ∧ x = H.op γ X₂ ∧ H.IsInv T.M T.d T.F α δ Y₂ γ X₂ := by
  obtain ⟨hγα, hδα, hδ0, hγδ, hX0, hXT, halt⟩ := hinv
  have hXT' : ∀ z, z ∈ X → z ∈ T.Ts γ := fun z hz =>
    (T.inT_iff (T.lower_suc hα hγα) hγα).mp (hXT z hz)
  obtain ⟨δ', Y0, Y₂, e1, e2, hY₂⟩ := hy
  obtain ⟨e3, e4⟩ := H.op_inj e1
  obtain ⟨γ', X0, X₂, e1', e2', hX₂⟩ := hx
  obtain ⟨e3', e4'⟩ := H.op_inj e1'
  rw [← e3] at e2 hY₂
  rw [← e4] at hY₂
  rw [← e3'] at e2' hX₂
  rw [← e4'] at hX₂
  refine ⟨Y₂, X₂, e2, e2', hγα, hδα, hδ0, hγδ, ?_, fun z hz => ?_,
    T.alt_transport hα hI hπ hγα hδα hδ0 hγδ hXT' halt hX₂ hY₂⟩
  · obtain ⟨z, hz⟩ := H.ne_emp hX0
    obtain ⟨z', -, hact⟩ := T.low_tot hα hI hπ hγα (hXT' z hz)
    exact fun h0 => H.not_mem_emp z' (h0 ▸ (hX₂ z').mpr ⟨z, hz, hact⟩)
  · obtain ⟨z0, hz0, hact⟩ := (hX₂ z).mp hz
    exact (T.inT_iff (T.lower_suc hα hγα) hγα).mpr
      (T.low_mem hα hI hπ hγα (hXT' z0 hz0) hact)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Retained pre-objects are sent to retained pre-objects. -/
theorem retained_transport {β π D D' : H.W} (hπ : H.IsAut T.M T.d T.F α π) (hβα : β ∈ α)
    (hD : ∀ z, z ∈ D → z ∈ T.Ts β) (hret : H.Retained T.M T.d T.F α β D)
    (hact : H.ActRaw T.F α π (H.op β D) (H.op β D')) : H.Retained T.M T.d T.F α β D' := by
  obtain ⟨n, s, K, hn, hs, hs0, hstep, ⟨δn, Yn, hsn, hterm⟩, hK⟩ := hret
  have hpre : ∀ i x, H.App s i x → T.Pre α x := by
    intro i x hix
    have hi : i ∈ H.suc n := (hs.2 i).mpr ⟨x, hix⟩
    have hio : i ∈ H.om := (H.om_trans _ (H.suc_mem_om hn) i hi).1
    rcases H.om_cases hio with e | ⟨m, -, e⟩
    · rw [e] at hix
      rw [hs.1.2 _ _ _ hix hs0]
      exact ⟨β, D, rfl, hβα, hD⟩
    · have hm : m ∈ n := by
        have hmi : m ∈ i := by
          rw [e]
          exact H.mem_suc.mpr (Or.inr rfl)
        rcases H.mem_suc.mp hi with h | h
        · exact H.om_mem_trans hn h hmi
        · rw [h] at hmi
          exact hmi
      obtain ⟨δ, Y, γ, X, -, h2, hinv⟩ := hstep m hm
      rw [← e] at h2
      rw [hs.1.2 _ _ _ hix h2]
      exact T.pre_of_inv hα hinv
  have hR : Def2 H (fun i y => ∃ x, H.App s i x ∧ H.ActRaw T.F α π x y) := by hdef
  have hfun : ∀ u ∈ H.suc n, ∀ v v', (∃ x, H.App s u x ∧ H.ActRaw T.F α π x v) →
      (∃ x, H.App s u x ∧ H.ActRaw T.F α π x v') → v = v' := by
    rintro u - v v' ⟨x, hx, hv⟩ ⟨x', hx', hv'⟩
    rw [hs.1.2 _ _ _ hx hx'] at hv
    exact actRaw_fun hv hv'
  obtain ⟨s₂, hs₂f, hs₂⟩ : ∃ s₂, H.IsFun s₂ ∧ ∀ i y, H.App s₂ i y ↔
      i ∈ H.suc n ∧ ∃ x, H.App s i x ∧ H.ActRaw T.F α π x y :=
    ⟨H.mkFun (H.suc n) _ hR hfun, H.isFun_mkFun, fun i y => H.app_mkFun⟩
  have happ : ∀ {i x y}, H.App s i x → H.ActRaw T.F α π x y → H.App s₂ i y :=
    fun hix hxy => (hs₂ _ _).mpr ⟨(hs.2 _).mpr ⟨_, hix⟩, _, hix, hxy⟩
  refine ⟨n, s₂, K, hn, ⟨hs₂f, fun i => ⟨fun hi => ?_, fun ⟨y, hy⟩ => ((hs₂ i y).mp hy).1⟩⟩,
    happ hs0 hact, fun i hi => ?_, ?_, hK⟩
  · obtain ⟨x, hx⟩ := (hs.2 i).mp hi
    obtain ⟨y, -, hy⟩ := T.raw_tot hα hI hπ (hpre i x hx)
    exact ⟨y, happ hx hy⟩
  · obtain ⟨δ, Y, γ, X, h1, h2, hinv⟩ := hstep i hi
    obtain ⟨y, -, hy⟩ := T.raw_tot hα hI hπ (hpre _ _ h1)
    obtain ⟨x, -, hx⟩ := T.raw_tot hα hI hπ (hpre _ _ h2)
    obtain ⟨Y₂, X₂, ey, ex, hinv₂⟩ := T.inv_transport hα hI hπ hinv hy hx
    rw [ey] at hy
    rw [ex] at hx
    exact ⟨δ, Y₂, γ, X₂, happ h1 hy, happ h2 hx, hinv₂⟩
  · obtain ⟨y, -, hy⟩ := T.raw_tot hα hI hπ (hpre _ _ hsn)
    obtain ⟨δ', Y0, Y₂, e1, e2, hY₂⟩ := id hy
    obtain ⟨e3, e4⟩ := H.op_inj e1
    rw [← e3] at e2
    rw [e2] at hy
    refine ⟨δn, Y₂, happ hsn hy, fun ⟨γ, X₂, hinv₂⟩ => ?_⟩
    obtain ⟨x', -, hx'⟩ := T.raw_tot hα hI (isAut_inv hπ) (T.pre_of_inv hα hinv₂)
    obtain ⟨Y₃, X₃, ey, -, hinv₃⟩ := T.inv_transport hα hI (isAut_inv hπ) hinv₂
      (T.raw_inv hα hI hπ (hpre _ _ hsn) hy) hx'
    rw [← (H.op_inj ey).2] at hinv₃
    exact hterm ⟨γ, X₃, hinv₃⟩

/-- The group of the stage acts on the objects of the stage. -/
theorem act_tot_stage {π x : H.W} (hπG : π ∈ T.Gs α) (hx : x ∈ T.Tp α) :
    ∃ y, y ∈ T.Tp α ∧ H.ActRaw T.F α π x y := by
  have hπ := (T.mem_Gs hα).mp hπG
  have hpre := T.obj_pre hα hx
  obtain ⟨y, hypre, hact⟩ := T.raw_tot hα hI hπ hpre
  refine ⟨y, ((T.spec hα).2.2.1 y).mpr ?_, hact⟩
  obtain ⟨hxMp, β, D, e, hform, Sp, hfin, htok, hsupp⟩ := ((T.spec hα).2.2.1 x).mp hx
  obtain ⟨β', D0, D', e1, e2, hD'⟩ := id hact
  obtain ⟨e3, e4⟩ := H.op_inj (e.symm.trans e1)
  rw [← e3] at e2 hD'
  rw [← e4] at hD'
  obtain ⟨Sp', hfin', hSp'⟩ := fin_image hfin hπ.1.1 (fun v hv => hπ.2.1 v (htok v hv))
  refine ⟨T.pre_mem_Mp hα hI hypre, β, D', e2, ?_, Sp', hfin', fun w hw => ?_,
    T.supp_conj hα hI hπ hpre hact hsupp (fun v hv => ?_)⟩
  · rcases hform with ⟨hD0, hβ0⟩ | ⟨hD0, hβα, hDT, hret⟩
    · refine Or.inl ⟨H.eq_emp fun z hz => ?_, hβ0⟩
      obtain ⟨z0, hz0, -⟩ := (hD' z).mp hz
      rw [hD0] at hz0
      exact H.not_mem_emp z0 hz0
    · have hDT' : ∀ z, z ∈ D → z ∈ T.Ts β := fun z hz =>
        (T.inT_iff (T.lower_suc hα hβα) hβα).mp (hDT z hz)
      refine Or.inr ⟨?_, hβα, fun z hz => ?_,
        T.retained_transport hα hI hπ hβα hDT' hret (by rw [← e, ← e2]; exact hact)⟩
      · obtain ⟨z, hz⟩ := H.ne_emp hD0
        obtain ⟨z', -, ha⟩ := T.low_tot hα hI hπ hβα (hDT' z hz)
        exact fun h0 => H.not_mem_emp z' (h0 ▸ (hD' z').mpr ⟨z, hz, ha⟩)
      · obtain ⟨z0, hz0, ha⟩ := (hD' z).mp hz
        exact (T.inT_iff (T.lower_suc hα hβα) hβα).mpr
          (T.low_mem hα hI hπ hβα (hDT' z0 hz0) ha)
  · obtain ⟨v, hv, hvw⟩ := (hSp' w).mp hw
    exact (hπ.1.2.1 _ _ hvw).2
  · obtain ⟨w, hw⟩ := hπ.2.1 v (htok v hv)
    exact ⟨w, (hSp' w).mpr ⟨v, hv, hw⟩, hw⟩

end stage

end Tower

end Host


/-! ## Parity, chains of inverses, injectivity of the alternate extensions, depth -/

namespace Host

variable {H : Host}

/-- `n` is even: there is a set of indices that contains `0` and `n` and alternates below `n`. -/
def Even (H : Host) (n : H.W) : Prop :=
  ∃ K : H.W, n ∈ K ∧ H.emp ∈ K ∧ ∀ i, i ∈ n → (i ∈ K ↔ ¬ H.suc i ∈ K)

theorem even_emp : H.Even H.emp :=
  ⟨H.sg H.emp, H.mem_sg.mpr rfl, H.mem_sg.mpr rfl, fun i hi => (H.not_mem_emp i hi).elim⟩

theorem even_suc_suc {n : H.W} (hn : n ∈ H.om) (h : H.Even n) : H.Even (H.suc (H.suc n)) := by
  obtain ⟨K, hK1, hK2, hK3⟩ := h
  obtain ⟨K0, hK0⟩ := H.sep' K (fun i => i ∈ H.suc n) (by hdef)
  have hmem : ∀ x, x ∈ H.bun K0 (H.sg (H.suc (H.suc n))) ↔
      (x ∈ K ∧ x ∈ H.suc n) ∨ x = H.suc (H.suc n) := fun x => by
    rw [H.mem_bun, H.mem_sg, hK0 x]
  have hnn : n ∈ H.suc n := H.mem_suc.mpr (Or.inr rfl)
  have hne : ∀ {j}, j ∈ H.suc n → j ≠ H.suc (H.suc n) := fun hj e => by
    rw [e] at hj
    exact H.mem_asymm (H.mem_suc.mpr (Or.inr rfl)) hj
  have hsn : ¬ H.suc n ∈ H.bun K0 (H.sg (H.suc (H.suc n))) := by
    rw [hmem]
    rintro (⟨-, h⟩ | h)
    · exact H.mem_irrefl _ h
    · have h1 : H.suc n ∈ H.suc (H.suc n) := H.mem_suc.mpr (Or.inr rfl)
      rw [← h] at h1
      exact H.mem_irrefl _ h1
  refine ⟨H.bun K0 (H.sg (H.suc (H.suc n))), (hmem _).mpr (Or.inr rfl),
    (hmem _).mpr (Or.inl ⟨hK2, ?_⟩), fun i hi => ?_⟩
  · rcases H.emp_mem_or hn with e | e
    · rw [e]
      exact H.mem_suc.mpr (Or.inr rfl)
    · exact H.mem_suc.mpr (Or.inl e)
  · rcases H.mem_suc.mp hi with hi | hi
    · rcases H.mem_suc.mp hi with hi | hi
      · have hi' : i ∈ H.suc n := H.mem_suc.mpr (Or.inl hi)
        have hsi : H.suc i ∈ H.suc n := (H.suc_mem_or n hn i hi).elim
          (fun h => H.mem_suc.mpr (Or.inl h)) (fun h => H.mem_suc.mpr (Or.inr h))
        rw [hmem, hmem]
        constructor
        · rintro (⟨h, -⟩ | h) (⟨h', -⟩ | h')
          · exact (hK3 i hi).mp h h'
          · exact hne hsi h'
          · exact (hne hi' h).elim
          · exact hne hsi h'
        · intro h
          refine Or.inl ⟨(hK3 i hi).mpr fun h' => h (Or.inl ⟨h', hsi⟩), hi'⟩
      · rw [hi]
        exact ⟨fun _ => hsn, fun _ => (hmem _).mpr (Or.inl ⟨hK1, hnn⟩)⟩
    · rw [hi]
      exact ⟨fun h => (hsn h).elim, fun h => (h ((hmem _).mpr (Or.inr rfl))).elim⟩

theorem even_excl {n : H.W} (hn : n ∈ H.om) (h : H.Even n) (h' : H.Even (H.suc n)) : False := by
  obtain ⟨K, hK1, hK2, hK3⟩ := h
  obtain ⟨K', hK1', hK2', hK3'⟩ := h'
  have key := H.om_ind (fun i => i ∈ H.suc n → (i ∈ K ↔ i ∈ K')) (by hdef)
    (fun _ => ⟨fun _ => hK2', fun _ => hK2⟩)
    (fun i _ ih hsi => by
      have hin : i ∈ n := by
        rcases H.mem_suc.mp hsi with h | h
        · exact H.om_mem_trans hn h (H.mem_suc.mpr (Or.inr rfl))
        · rw [← h]
          exact H.mem_suc.mpr (Or.inr rfl)
      have h1 := hK3 i hin
      have h2 := hK3' i (H.mem_suc.mpr (Or.inl hin))
      have h3 := ih (H.mem_suc.mpr (Or.inl hin))
      constructor
      · intro hs
        by_contra hs'
        exact (h1.mp (h3.mpr (h2.mpr hs'))) hs
      · intro hs
        by_contra hs'
        exact (h2.mp (h3.mp (h1.mpr hs'))) hs)
  have hnK' : n ∈ K' := (key n hn (H.mem_suc.mpr (Or.inr rfl))).mp hK1
  exact (hK3' n (H.mem_suc.mpr (Or.inr rfl))).mp hnK' hK1'

/-- `s` is the chain of inverses of `(β, D)`, of length `n`. -/
def IsChain (H : Host) (M d F α β D n s : H.W) : Prop :=
  n ∈ H.om ∧ H.FunOn s (H.suc n) ∧ H.App s H.emp (H.op β D) ∧
    (∀ i, i ∈ n → ∃ δ Y γ X, H.App s i (H.op δ Y) ∧ H.App s (H.suc i) (H.op γ X) ∧
      H.IsInv M d F α δ Y γ X) ∧
    (∃ δ Y, H.App s n (H.op δ Y) ∧ ¬ ∃ γ X, H.IsInv M d F α δ Y γ X)

theorem retained_iff {M d F α β D : H.W} :
    H.Retained M d F α β D ↔ ∃ n s, H.IsChain M d F α β D n s ∧ H.Even n := by
  constructor
  · rintro ⟨n, s, K, h1, h2, h3, h4, h5, h6⟩
    exact ⟨n, s, ⟨h1, h2, h3, h4, h5⟩, K, h6⟩
  · rintro ⟨n, s, ⟨h1, h2, h3, h4, h5⟩, K, h6⟩
    exact ⟨n, s, K, h1, h2, h3, h4, h5, h6⟩

theorem chain_nil {M d F α β D : H.W} (h : ¬ ∃ γ X, H.IsInv M d F α β D γ X) :
    H.IsChain M d F α β D H.emp (H.ins H.emp H.emp (H.op β D)) :=
  ⟨H.emp_mem_om, H.funOn_ins H.funOn_emp, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩),
    fun i hi => (H.not_mem_emp i hi).elim, β, D, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩), h⟩

theorem chain_cons {M d F α δ Y γ X n s : H.W} (hinv : H.IsInv M d F α δ Y γ X)
    (h : H.IsChain M d F α γ X n s) : ∃ s', H.IsChain M d F α δ Y (H.suc n) s' := by
  obtain ⟨hn, hs, hs0, hstep, hterm⟩ := h
  have hR : Def2 H (fun i v => (i = H.emp ∧ v = H.op δ Y) ∨ ∃ j, i = H.suc j ∧ H.App s j v) := by
    hdef
  have hfun : ∀ u ∈ H.suc (H.suc n), ∀ v v',
      ((u = H.emp ∧ v = H.op δ Y) ∨ ∃ j, u = H.suc j ∧ H.App s j v) →
      ((u = H.emp ∧ v' = H.op δ Y) ∨ ∃ j, u = H.suc j ∧ H.App s j v') → v = v' := by
    rintro u - v v' (⟨e, ev⟩ | ⟨j, e, hj⟩) (⟨e', ev'⟩ | ⟨j', e', hj'⟩)
    · rw [ev, ev']
    · exact (H.suc_ne_emp j' (e'.symm.trans e)).elim
    · exact (H.suc_ne_emp j (e.symm.trans e')).elim
    · rw [H.suc_inj (e.symm.trans e')] at hj
      exact hs.1.2 _ _ _ hj hj'
  obtain ⟨s', hs'f, hs'⟩ : ∃ s', H.IsFun s' ∧ ∀ i v, H.App s' i v ↔ i ∈ H.suc (H.suc n) ∧
      ((i = H.emp ∧ v = H.op δ Y) ∨ ∃ j, i = H.suc j ∧ H.App s j v) :=
    ⟨H.mkFun (H.suc (H.suc n)) _ hR hfun, H.isFun_mkFun, fun i v => H.app_mkFun⟩
  have hsn : H.suc n ∈ H.om := H.suc_mem_om hn
  have h0 : H.App s' H.emp (H.op δ Y) :=
    (hs' _ _).mpr ⟨(H.emp_mem_or (H.suc_mem_om hsn)).resolve_left (H.suc_ne_emp _),
      Or.inl ⟨rfl, rfl⟩⟩
  have hsucmem : ∀ {j}, j ∈ H.suc n → H.suc j ∈ H.suc (H.suc n) := fun hj =>
    (H.suc_mem_or _ hsn _ hj).elim (fun h => H.mem_suc.mpr (Or.inl h))
      (fun h => H.mem_suc.mpr (Or.inr h))
  have hS : ∀ {j v}, H.App s j v → H.App s' (H.suc j) v := fun hj =>
    (hs' _ _).mpr ⟨hsucmem ((hs.2 _).mpr ⟨_, hj⟩), Or.inr ⟨_, rfl, hj⟩⟩
  refine ⟨s', hsn, ⟨hs'f, fun i => ⟨fun hi => ?_, fun ⟨v, hv⟩ => ((hs' i v).mp hv).1⟩⟩, h0,
    fun i hi => ?_, ?_⟩
  · have hio : i ∈ H.om := (H.om_trans _ (H.suc_mem_om hsn) i hi).1
    rcases H.om_cases hio with e | ⟨m, -, e⟩
    · rw [e]
      exact ⟨_, h0⟩
    · have hm : m ∈ H.suc n := by
        rw [e] at hi
        rcases H.mem_suc.mp hi with h | h
        · exact H.om_mem_trans hsn h (H.mem_suc.mpr (Or.inr rfl))
        · rw [H.suc_inj h]
          exact H.mem_suc.mpr (Or.inr rfl)
      obtain ⟨v, hv⟩ := (hs.2 m).mp hm
      rw [e]
      exact ⟨v, hS hv⟩
  · have hio : i ∈ H.om := (H.om_trans _ hsn i hi).1
    rcases H.om_cases hio with e | ⟨m, -, e⟩
    · rw [e]
      exact ⟨δ, Y, γ, X, h0, hS hs0, hinv⟩
    · have hm : m ∈ n := by
        rw [e] at hi
        rcases H.mem_suc.mp hi with h | h
        · exact H.om_mem_trans hn h (H.mem_suc.mpr (Or.inr rfl))
        · rw [← h]
          exact H.mem_suc.mpr (Or.inr rfl)
      obtain ⟨δ', Y', γ', X', h1, h2, hinv'⟩ := hstep m hm
      rw [e]
      exact ⟨δ', Y', γ', X', hS h1, hS h2, hinv'⟩
  · obtain ⟨δ', Y', h1, h2⟩ := hterm
    exact ⟨δ', Y', hS h1, h2⟩

theorem chain_len_le {M d F α β D n s m t : H.W}
    (huniq : ∀ δ Y γ X γ' X', H.IsInv M d F α δ Y γ X → H.IsInv M d F α δ Y γ' X' →
      γ = γ' ∧ X = X')
    (h : H.IsChain M d F α β D n s) (h' : H.IsChain M d F α β D m t) : n ∈ H.suc m := by
  obtain ⟨hn, hs, hs0, hstep, -⟩ := h
  obtain ⟨hm, ht, ht0, hstep', δm, Ym, htm, htermm⟩ := h'
  have key := H.om_ind
    (fun i => i ∈ H.suc n → i ∈ H.suc m ∧ ∃ v, H.App s i v ∧ H.App t i v) (by hdef)
    (fun _ => ⟨(H.emp_mem_or (H.suc_mem_om hm)).resolve_left (H.suc_ne_emp _), _, hs0, ht0⟩)
    (fun i _ ih hsi => by
      have hin : i ∈ n := by
        rcases H.mem_suc.mp hsi with h | h
        · exact H.om_mem_trans hn h (H.mem_suc.mpr (Or.inr rfl))
        · rw [← h]
          exact H.mem_suc.mpr (Or.inr rfl)
      obtain ⟨him, v, hv, hv'⟩ := ih (H.mem_suc.mpr (Or.inl hin))
      obtain ⟨δ, Y, γ, X, h1, h2, hinv⟩ := hstep i hin
      rw [hs.1.2 _ _ _ hv h1] at hv'
      have him' : i ∈ m := by
        rcases H.mem_suc.mp him with h | h
        · exact h
        · rw [h] at hv'
          obtain ⟨e1, e2⟩ := H.op_inj (ht.1.2 _ _ _ hv' htm)
          rw [e1, e2] at hinv
          exact (htermm ⟨γ, X, hinv⟩).elim
      obtain ⟨δ', Y', γ', X', h1', h2', hinv'⟩ := hstep' i him'
      obtain ⟨e1, e2⟩ := H.op_inj (ht.1.2 _ _ _ hv' h1')
      rw [← e1, ← e2] at hinv'
      obtain ⟨e3, e4⟩ := huniq _ _ _ _ _ _ hinv hinv'
      rw [← e3, ← e4] at h2'
      exact ⟨(H.suc_mem_or _ hm _ him').elim (fun h => H.mem_suc.mpr (Or.inl h))
        (fun h => H.mem_suc.mpr (Or.inr h)), _, h2, h2'⟩)
  exact (key n hn (H.mem_suc.mpr (Or.inr rfl))).1

/-- A pre-object is retained, or its inverse is. -/
def GoodPre (H : Host) (M d F α γ X : H.W) : Prop :=
  H.Retained M d F α γ X ∨ ∃ γ' X', H.IsInv M d F α γ X γ' X' ∧ H.Retained M d F α γ' X'

theorem good_of_no_inv {M d F α γ X : H.W} (h : ¬ ∃ γ' X', H.IsInv M d F α γ X γ' X') :
    H.GoodPre M d F α γ X :=
  Or.inl (retained_iff.mpr ⟨_, _, chain_nil h, even_emp⟩)

theorem good_step {M d F α γ X γ' X' : H.W} (hinv : H.IsInv M d F α γ X γ' X')
    (h : H.GoodPre M d F α γ' X') : H.GoodPre M d F α γ X := by
  rcases h with h | ⟨γ₃, X₃, hinv', hret⟩
  · exact Or.inr ⟨γ', X', hinv, h⟩
  · obtain ⟨n, s, hch, hev⟩ := retained_iff.mp hret
    obtain ⟨s1, hch1⟩ := chain_cons hinv' hch
    obtain ⟨s2, hch2⟩ := chain_cons hinv hch1
    exact Or.inl (retained_iff.mpr ⟨_, s2, hch2, even_suc_suc hch.1 hev⟩)

namespace Tower

variable (T : Tower H)

theorem name_mem_M {γ c : H.W} (hγd : γ ∈ T.d) (hIγ : T.InvT γ) (hc : c ∈ T.Ns γ) : c ∈ T.M := by
  obtain ⟨La, hLa, hcL⟩ := hIγ.names c hc
  have hd0 : T.d ≠ H.emp := fun e => H.not_mem_emp γ (e ▸ hγd)
  rcases H.suc_mem_or _ T.hd _ hγd with h | h
  · exact T.hM.trans _ _ hcL (T.mono _ _ _ _ hLa (T.hMd hd0) h)
  · rw [h] at hLa
    rw [T.hΛ.2 _ _ _ hLa (T.hMd hd0)] at hcL
    exact hcL

theorem tup_mem_M {β S : H.W} (h : H.IsTup T.M T.d β S) : S ∈ T.M := by
  obtain ⟨n, hn, hS, htok⟩ := h
  exact T.hM.fun_mem hS (T.hM.nat_mem hn) (fun a b hab => tok_mem T.hM T.hdM (htok a b hab))

/-- The entries of a tuple of a descriptor that decodes to a literal litter are not all below
the label of the litter. -/
theorem lit_in_closure {β c S y c' : H.W} (hβ : T.Proper β) (hIβ : T.InvT β)
    (hq : H.op c (H.op S y) ∈ T.Ds β) (hc' : H.IsLabel T.M c') (hy : H.IsLit T.M c' y) :
    ∃ j s u, H.App S j (H.op s u) ∧ ¬ H.lt s c' := by
  by_contra hcon
  have hlt : ∀ j s u, H.App S j (H.op s u) → H.lt s c' := fun j s u hj => by
    by_contra h
    exact hcon ⟨j, s, u, hj, h⟩
  have hdesc := (hIβ.dec_mem c S y hq).2
  obtain ⟨n, hn, hS⟩ := desc_fun hdesc
  obtain ⟨π, hπ, -, hfix, hmove⟩ := move (F := T.F) T.hM T.hdM (T.proper_om hβ) hn hS
    (fun j q hj => desc_tok hdesc hj) (T.tok_label_top hβ hc') hlt
  have hact := hIβ.dec_supp c S y hq π ((T.mem_Gs hβ).mpr hπ) hfix
  obtain ⟨w, hw⟩ := hπ.2.1 _ (T.tok_label_top hβ hc')
  obtain ⟨c'', e⟩ := piso_mid hπ.1 hw
  rw [e] at hw
  have hc''M : c'' ∈ T.M := (T.hM.of_op_mem (tok_mem T.hM T.hdM (hπ.1.2.1 _ _ hw).2)).1
  obtain ⟨y'', hy''⟩ := H.lit_ex T.M c''
  have e2 : y = y'' := actRaw_fun hact (T.lit_act hβ hπ hc' hw hy hy'')
  rw [← e2] at hy''
  rw [← lit_inj T.hM hc'.1 hc''M hy hy''] at hw
  exact hmove hw

section stage

variable {α : H.W} (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

omit hI in
theorem lvl_mem {γ : H.W} (hγα : γ ∈ α) : γ ∈ T.M := T.hM.trans _ _ (T.lower_suc hα hγα) T.hdM

theorem desc_mem_M {γ c S : H.W} (hγα : γ ∈ α) (h : H.Desc T.M T.d T.F α γ c S) :
    c ∈ T.M ∧ S ∈ T.M := by
  rcases h with ⟨-, k, i, ec, hk, hi, hS, htok⟩ | ⟨h0, hN, hS, -⟩
  · refine ⟨?_, T.hM.fun_mem hS (T.hM.nat_mem hk)
      (fun a b hab => tok_mem T.hM T.hdM (htok a b hab))⟩
    rw [ec]
    exact T.hM.op_mem (T.hM.nat_mem hk) (T.hM.trans _ _ hi (T.hM.nat_mem hk))
  · have hγ := T.lower_proper hα hγα h0
    exact ⟨T.name_mem_M (T.lower_mem_d hα hγα) (hI γ hγα hγ) ((T.inN_iff hγ hγα).mp hN),
      T.tup_mem_M hS⟩

/-- Every object of a lower level has a descriptor. -/
theorem ex_desc {γ x : H.W} (hγα : γ ∈ α) (hx : x ∈ T.Ts γ) :
    ∃ c S, H.Desc T.M T.d T.F α γ c S ∧ H.InD T.M T.d T.F α γ c S x := by
  by_cases hγ0 : γ = H.emp
  · subst hγ0
    have hxa := T.mem_Ts_emp.mp hx
    have hS : H.FunOn (H.ins H.emp H.emp (H.op x H.emp)) H.one := H.funOn_ins H.funOn_emp
    have hdesc : H.Desc T.M T.d T.F α H.emp (H.op H.one H.emp)
        (H.ins H.emp H.emp (H.op x H.emp)) :=
      Or.inl ⟨rfl, H.one, H.emp, rfl, H.one_mem_om, H.mem_one.mpr rfl, hS, fun j v hj => by
        rcases H.app_ins.mp hj with h | ⟨-, e⟩
        · exact (H.not_mem_emp _ (H.app_iff.mp h)).elim
        · rw [e]
          exact ⟨x, H.emp, rfl, fun y hy => (H.not_mem_emp y hy).elim, Or.inl ⟨rfl, rfl⟩,
            Or.inl hxa⟩⟩
    exact ⟨_, _, hdesc, Or.inl ⟨rfl, hdesc, H.one, H.emp, rfl,
      H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩)⟩⟩
  · have hγ := T.lower_proper hα hγα hγ0
    rw [T.Ts_of_ne hγ0] at hx
    obtain ⟨c, S, hq⟩ := (hI γ hγα hγ).dec_surj x hx
    exact ⟨c, S, (desc_stage (β := H.suc γ) (H.mem_suc.mpr (Or.inr rfl)) hγα).mp
      ((hI γ hγα hγ).dec_mem c S x hq).2, (T.inD_iff hγ hγα).mpr hq⟩

theorem inD_fun {γ c S x x' : H.W} (hγα : γ ∈ α) (h : H.InD T.M T.d T.F α γ c S x)
    (h' : H.InD T.M T.d T.F α γ c S x') : x = x' := by
  by_cases hγ0 : γ = H.emp
  · rcases h with ⟨-, hdesc, k, i, ec, hi⟩ | ⟨h0, -⟩
    · rcases h' with ⟨-, -, k', i', ec', hi'⟩ | ⟨h0', -⟩
      · rw [← (H.op_inj (ec.symm.trans ec')).2] at hi'
        obtain ⟨n, -, hS⟩ := desc_fun hdesc
        exact (H.op_inj (hS.1.2 _ _ _ hi hi')).1
      · exact (h0' hγ0).elim
    · exact (h0 hγ0).elim
  · have hγ := T.lower_proper hα hγα hγ0
    exact (hI γ hγα hγ).dec_fun c S x x' ((T.inD_iff hγ hγα).mp h) ((T.inD_iff hγ hγα).mp h')

/-- The alternate extension of a nonempty set determines the source level, and is monotone. -/
theorem alt_sub {γ γ' δ X X' Y : H.W} (hγα : γ ∈ α) (hδα : δ ∈ α)
    (hX : ∀ z, z ∈ X → z ∈ T.Ts γ) (hX0 : X ≠ H.emp)
    (hY : H.IsAlt T.M T.d T.F α γ δ X Y) (hY' : H.IsAlt T.M T.d T.F α γ' δ X' Y) :
    γ = γ' ∧ H.Sub X X' := by
  have step : ∀ x, x ∈ X → γ = γ' ∧ x ∈ X' := by
    intro x hx
    obtain ⟨c, S, hdesc, hdec⟩ := T.ex_desc hα hI hγα (hX x hx)
    obtain ⟨hcM, hSM⟩ := T.desc_mem_M hα hI hγα hdesc
    have hbM : H.label (H.op γ δ) (H.op c S) H.emp H.emp ∈ T.M :=
      T.hM.label_mem (T.hM.op_mem (T.lvl_mem hα hγα) (T.lvl_mem hα hδα)) (T.hM.op_mem hcM hSM)
        T.hM.emp_mem T.hM.emp_mem
    obtain ⟨l, hl⟩ := H.lit_ex T.M (H.label (H.op γ δ) (H.op c S) H.emp H.emp)
    have hlY : l ∈ Y := (hY l).mpr ⟨c, S, _, _, x, hdesc, hdec, hx, hbM, hl⟩
    obtain ⟨c', S', X'', η'', x', hdesc', hdec', hx', hb'M, hl'⟩ := (hY' l).mp hlY
    obtain ⟨e1, e2, -, -⟩ := H.label_inj (lit_inj T.hM hbM hb'M hl hl')
    have eγ : γ = γ' := (H.op_inj e1).1
    obtain ⟨ec, eS⟩ := H.op_inj e2
    rw [← eγ, ← ec, ← eS] at hdec'
    rw [T.inD_fun hα hI hγα hdec hdec']
    exact ⟨eγ, hx'⟩
  obtain ⟨x, hx⟩ := H.ne_emp hX0
  exact ⟨(step x hx).1, fun z hz => (step z hz).2⟩

/-- The partial inverse is unique. -/
theorem inv_unique {δ Y γ X γ' X' : H.W} (h : H.IsInv T.M T.d T.F α δ Y γ X)
    (h' : H.IsInv T.M T.d T.F α δ Y γ' X') : γ = γ' ∧ X = X' := by
  obtain ⟨hγα, hδα, -, -, hX0, hXT, halt⟩ := h
  obtain ⟨hγ'α, -, -, -, hX0', hXT', halt'⟩ := h'
  have h1 := T.alt_sub hα hI hγα hδα
    (fun z hz => (T.inT_iff (T.lower_suc hα hγα) hγα).mp (hXT z hz)) hX0 halt halt'
  have h2 := T.alt_sub hα hI hγ'α hδα
    (fun z hz => (T.inT_iff (T.lower_suc hα hγ'α) hγ'α).mp (hXT' z hz)) hX0' halt' halt
  exact ⟨h1.1, H.sub_antisymm h1.2 h2.2⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- **Chains of inverses are finite.** Every pre-object is retained or has a retained
inverse. -/
theorem good_all (γ X : H.W) : H.GoodPre T.M T.d T.F α γ X := by
  have Q : ∀ b, ∀ γ X l, H.IsLabel T.M b → H.IsLit T.M b l → l ∈ X →
      H.GoodPre T.M T.d T.F α γ X := by
    refine H.lt_ind _ (by hdef) ?_
    intro b ih γ X l hb hl hlX
    by_cases h1 : ∃ γ' X', H.IsInv T.M T.d T.F α γ X γ' X'
    · obtain ⟨γ', X', hinv⟩ := h1
      refine good_step hinv ?_
      by_cases h2 : ∃ γ'' X'', H.IsInv T.M T.d T.F α γ' X' γ'' X''
      · obtain ⟨γ'', X'', hinv'⟩ := h2
        obtain ⟨c, S, X0, η0, x, hdesc, hdec, hx, hbM, hlit⟩ := (hinv.2.2.2.2.2.2 l).mp hlX
        have eb := lit_inj T.hM hb.1 hbM hl hlit
        obtain ⟨c2, S2, X2, η2, x2, -, -, -, hc'M, hxlit⟩ := (hinv'.2.2.2.2.2.2 x).mp hx
        obtain ⟨c', hc'⟩ : ∃ c', c' = H.label (H.op γ'' γ') (H.op c2 S2) X2 η2 := ⟨_, rfl⟩
        rw [← hc'] at hc'M hxlit
        have hc'l : H.IsLabel T.M c' := ⟨hc'M, _, _, _, _, hc'⟩
        have hγ'α := hinv.1
        have hγ' := T.lower_proper hα hγ'α hinv'.2.2.1
        have hq := (T.inD_iff hγ' hγ'α).mp hdec
        obtain ⟨j, s, u, hj, hnlt⟩ := T.lit_in_closure hγ' (hI γ' hγ'α hγ') hq hc'l hxlit
        have hsb : H.lt s b := by
          rw [eb]
          exact H.lt_trans _ _ _ (H.lt_op_left s u) (H.lt_trans _ _ _ (H.app_lt_right hj)
            (H.lt_trans _ _ _ (H.lt_op_right c S) (H.lt_label_xi _ _ _ _)))
        have hc'b : H.lt c' b := by
          rcases H.lt_tri s c' with h | h | h
          · exact (hnlt h).elim
          · rw [← h]
            exact hsb
          · exact H.lt_trans _ _ _ h hsb
        exact ih c' hc'b γ' X' x hc'l hxlit hx
      · exact good_of_no_inv h2
    · exact good_of_no_inv h1
  by_cases h1 : ∃ γ' X', H.IsInv T.M T.d T.F α γ X γ' X'
  · obtain ⟨γ', X', hinv⟩ := h1
    obtain ⟨x, hx⟩ := H.ne_emp hinv.2.2.2.2.1
    have hxT := (T.inT_iff (T.lower_suc hα hinv.1) hinv.1).mp (hinv.2.2.2.2.2.1 x hx)
    obtain ⟨c, S, hdesc, hdec⟩ := T.ex_desc hα hI hinv.1 hxT
    obtain ⟨hcM, hSM⟩ := T.desc_mem_M hα hI hinv.1 hdesc
    have hbM : H.label (H.op γ' γ) (H.op c S) H.emp H.emp ∈ T.M :=
      T.hM.label_mem (T.hM.op_mem (T.lvl_mem hα hinv.1) (T.lvl_mem hα hinv.2.1))
        (T.hM.op_mem hcM hSM) T.hM.emp_mem T.hM.emp_mem
    obtain ⟨l, hl⟩ := H.lit_ex T.M (H.label (H.op γ' γ) (H.op c S) H.emp H.emp)
    exact Q _ γ X l ⟨hbM, _, _, _, _, rfl⟩ hl
      ((hinv.2.2.2.2.2.2 l).mpr ⟨c, S, _, _, x, hdesc, hdec, hx, hbM, hl⟩)
  · exact good_of_no_inv h1

end stage

end Tower

end Host


/-! ## Extensions, extensionality and symmetric comprehension at a stage -/

namespace Host

variable {H : Host}

theorem actRaw_emp {F α π : H.W} : H.ActRaw F α π (H.op H.emp H.emp) (H.op H.emp H.emp) :=
  ⟨H.emp, H.emp, H.emp, rfl, rfl, fun z' => ⟨fun h => (H.not_mem_emp z' h).elim,
    fun ⟨z, hz, _⟩ => (H.not_mem_emp z hz).elim⟩⟩

namespace Tower

variable (T : Tower H)

/-- `E` is the extension of the pre-object `x` at the level `δ`. -/
def Ext (α x δ E : H.W) : Prop :=
  ∃ β D, x = H.op β D ∧ ((β = δ ∧ E = D) ∨ (β ≠ δ ∧ H.IsAlt T.M T.d T.F α β δ D E))

section stage

variable {α : H.W} (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

omit hI in
theorem obj_cases {x : H.W} (hx : x ∈ T.Tp α) : x = H.op H.emp H.emp ∨
    ∃ β D, x = H.op β D ∧ D ≠ H.emp ∧ β ∈ α ∧ (∀ z, z ∈ D → z ∈ T.Ts β) ∧
      H.Retained T.M T.d T.F α β D := by
  obtain ⟨-, β, D, e, ⟨hD, hβ⟩ | ⟨hD0, hβα, hDT, hret⟩, -⟩ := ((T.spec hα).2.2.1 x).mp hx
  · left
    rw [e, hD, hβ]
  · exact Or.inr ⟨β, D, e, hD0, hβα,
      fun z hz => (T.inT_iff (T.lower_suc hα hβα) hβα).mp (hDT z hz), hret⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
omit hI in
/-- The alternate extension exists and consists of objects of the target level. -/
theorem alt_ex {β δ D : H.W} (hδα : δ ∈ α) (hδ0 : δ ≠ H.emp) :
    ∃ E, H.IsAlt T.M T.d T.F α β δ D E ∧ ∀ z, z ∈ E → z ∈ T.Tp δ := by
  have hδ := T.lower_proper hα hδα hδ0
  obtain ⟨E, hE⟩ := H.sep' (T.Tp δ) (fun l => ∃ c S X' η x, H.Desc T.M T.d T.F α β c S ∧
    H.InD T.M T.d T.F α β c S x ∧ x ∈ D ∧ H.label (H.op β δ) (H.op c S) X' η ∈ T.M ∧
    H.IsLit T.M (H.label (H.op β δ) (H.op c S) X' η) l) (by hdef)
  refine ⟨E, fun l => ⟨fun h => ((hE l).mp h).2, fun h => (hE l).mpr ⟨?_, h⟩⟩,
    fun z hz => ((hE z).mp hz).1⟩
  obtain ⟨c, S, X', η, x, -, -, -, hbM, hl⟩ := h
  exact T.lit_mem hδ ⟨hbM, _, _, _, _, rfl⟩ hl

/-- **Extensionality.** Two objects of a stage with the same nonempty extension at a proper
lower level are equal. -/
theorem ext_stage {x y δ E : H.W} (hx : x ∈ T.Tp α) (hy : y ∈ T.Tp α) (hδα : δ ∈ α)
    (hδ0 : δ ≠ H.emp) (hEx : T.Ext α x δ E) (hEy : T.Ext α y δ E) (hE0 : E ≠ H.emp) : x = y := by
  have nonemp : ∀ {x β D : H.W}, x ∈ T.Tp α → x = H.op β D →
      ((β = δ ∧ E = D) ∨ (β ≠ δ ∧ H.IsAlt T.M T.d T.F α β δ D E)) →
      D ≠ H.emp ∧ β ∈ α ∧ (∀ z, z ∈ D → z ∈ T.Ts β) ∧ H.Retained T.M T.d T.F α β D := by
    intro x β D hx e hE
    have hD0 : D ≠ H.emp := by
      rcases hE with ⟨-, e'⟩ | ⟨-, halt⟩
      · rw [← e']
        exact hE0
      · intro h0
        obtain ⟨l, hl⟩ := H.ne_emp hE0
        obtain ⟨c, S, X', η, z, -, -, hz, -⟩ := (halt l).mp hl
        rw [h0] at hz
        exact H.not_mem_emp z hz
    rcases T.obj_cases hα hx with h | ⟨β', D', e', hD', hβα, hDT, hret⟩
    · obtain ⟨-, e2⟩ := H.op_inj (e.symm.trans h)
      exact (hD0 e2).elim
    · obtain ⟨e1, e2⟩ := H.op_inj (e.symm.trans e')
      rw [e1, e2]
      exact ⟨hD', hβα, hDT, hret⟩
  obtain ⟨β, D, ex, hEx⟩ := hEx
  obtain ⟨β', D', ey, hEy⟩ := hEy
  obtain ⟨hD0, hβα, hDT, hret⟩ := nonemp hx ex hEx
  obtain ⟨hD0', hβ'α, hDT', hret'⟩ := nonemp hy ey hEy
  have mixed : ∀ {β' D D' : H.W}, β' ≠ δ → H.IsAlt T.M T.d T.F α β' δ D' D → D' ≠ H.emp →
      β' ∈ α → (∀ z, z ∈ D' → z ∈ T.Ts β') → H.Retained T.M T.d T.F α β' D' →
      H.Retained T.M T.d T.F α δ D → False := by
    intro β' D D' hne halt hD0' hβ'α hDT' hret' hret
    have hinv : H.IsInv T.M T.d T.F α δ D β' D' := ⟨hβ'α, hδα, hδ0, hne, hD0',
      fun z hz => (T.inT_iff (T.lower_suc hα hβ'α) hβ'α).mpr (hDT' z hz), halt⟩
    obtain ⟨n, s, hch, hev⟩ := retained_iff.mp hret
    obtain ⟨n', s', hch', hev'⟩ := retained_iff.mp hret'
    obtain ⟨s'', hch''⟩ := chain_cons hinv hch'
    have huniq := fun δ Y γ X γ' X' (h : H.IsInv T.M T.d T.F α δ Y γ X)
      (h' : H.IsInv T.M T.d T.F α δ Y γ' X') => T.inv_unique hα hI h h'
    have h1 := chain_len_le huniq hch hch''
    have h2 := chain_len_le huniq hch'' hch
    have e : n = H.suc n' := by
      rcases H.mem_suc.mp h1 with h | h
      · rcases H.mem_suc.mp h2 with h' | h'
        · exact (H.mem_asymm h h').elim
        · exact h'.symm
      · exact h
    rw [e] at hev
    exact even_excl hch'.1 hev' hev
  rcases hEx with ⟨e1, e2⟩ | ⟨hne, halt⟩
  · rcases hEy with ⟨e1', e2'⟩ | ⟨hne', halt'⟩
    · rw [ex, ey, e1, e1', ← e2, ← e2']
    · rw [e2] at halt'
      rw [e1] at hret
      exact (mixed hne' halt' hD0' hβ'α hDT' hret' hret).elim
  · rcases hEy with ⟨e1', e2'⟩ | ⟨hne', halt'⟩
    · rw [e2'] at halt
      rw [e1'] at hret'
      exact (mixed hne halt hD0 hβα hDT hret hret').elim
    · have h1 := T.alt_sub hα hI hβα hδα hDT hD0 halt halt'
      have h2 := T.alt_sub hα hI hβ'α hδα hDT' hD0' halt' halt
      rw [ex, ey, h1.1, H.sub_antisymm h1.2 h2.2]

/-- **Symmetric comprehension.** A set of objects of a lower level that is stabilised by the
automorphisms fixing a finite set of tokens is the extension of an object that this set
supports. -/
theorem symm_comp {β X Sp : H.W} (hβα : β ∈ α) (hX : ∀ z, z ∈ X → z ∈ T.Ts β)
    (hfin : H.Fin Sp) (htok : ∀ v, v ∈ Sp → H.IsTok T.M T.d α v)
    (hstab : ∀ π, H.IsAut T.M T.d T.F α π → (∀ v, v ∈ Sp → H.App π v v) →
      ∀ z z', z ∈ X → H.ActLow T.F α π β z z' → z' ∈ X) :
    ∃ x, x ∈ T.Tp α ∧ H.SuppSet T.F (T.Gs α) α Sp x ∧
      ((X = H.emp ∧ x = H.op H.emp H.emp) ∨ x = H.op β X ∨
        ∃ β' X', x = H.op β' X' ∧ H.IsInv T.M T.d T.F α β X β' X') := by
  have hfixX : ∀ π, π ∈ T.Gs α → (∀ v, v ∈ Sp → H.App π v v) →
      H.ActRaw T.F α π (H.op β X) (H.op β X) := by
    intro π hπG hfix
    have hπ := (T.mem_Gs hα).mp hπG
    refine ⟨β, X, X, rfl, rfl, fun z' => ⟨fun hz' => ?_,
      fun ⟨z, hz, hact⟩ => hstab π hπ hfix z z' hz hact⟩⟩
    obtain ⟨z, -, hact⟩ := T.low_tot hα hI (isAut_inv hπ) hβα (hX z' hz')
    have hz : z ∈ X :=
      hstab _ (isAut_inv hπ) (fun v hv => app_inv.mpr (hfix v hv)) z' z hz' hact
    have h3 := T.low_inv hα hI (isAut_inv hπ) hβα (hX z' hz') hact
    rw [inv_inv hπ.1.1.1] at h3
    exact ⟨z, hz, h3⟩
  by_cases hX0 : X = H.emp
  · exact ⟨H.op H.emp H.emp, ((T.spec hα).2.2.1 _).mpr
      ⟨T.hMp.op_mem T.hMp.emp_mem T.hMp.emp_mem, H.emp, H.emp, rfl, Or.inl ⟨rfl, rfl⟩, Sp,
        hfin, htok, fun π _ _ => actRaw_emp⟩, fun π _ _ => actRaw_emp, Or.inl ⟨hX0, rfl⟩⟩
  · have hInT : ∀ z, z ∈ X → H.InT T.M T.F α β z := fun z hz =>
      (T.inT_iff (T.lower_suc hα hβα) hβα).mpr (hX z hz)
    rcases T.good_all hα hI β X with hret | ⟨β', X', hinv, hret⟩
    · exact ⟨H.op β X, ((T.spec hα).2.2.1 _).mpr ⟨T.pre_mem_Mp hα hI ⟨β, X, rfl, hβα, hX⟩,
        β, X, rfl, Or.inr ⟨hX0, hβα, hInT, hret⟩, Sp, hfin, htok, hfixX⟩, hfixX,
        Or.inr (Or.inl rfl)⟩
    · have hpre := T.pre_of_inv hα hinv
      have hsupp : H.SuppSet T.F (T.Gs α) α Sp (H.op β' X') := by
        intro π hπG hfix
        have hπ := (T.mem_Gs hα).mp hπG
        obtain ⟨y, -, hy⟩ := T.raw_tot hα hI hπ hpre
        obtain ⟨Y₂, X₂, e1, e2, hinv₂⟩ := T.inv_transport hα hI hπ hinv (hfixX π hπG hfix) hy
        rw [← (H.op_inj e1).2] at hinv₂
        rw [e2, ← (T.inv_unique hα hI hinv hinv₂).2] at hy
        exact hy
      exact ⟨H.op β' X', ((T.spec hα).2.2.1 _).mpr ⟨T.pre_mem_Mp hα hI hpre, β', X', rfl,
        Or.inr ⟨hinv.2.2.2.2.1, hinv.1, hinv.2.2.2.2.2.1, hret⟩, Sp, hfin, htok, hsupp⟩, hsupp,
        Or.inr (Or.inr ⟨β', X', rfl, hinv⟩)⟩

end stage

end Tower

end Host


/-! ## Conjugation into the sub-pool, and equivariance of the decoding from a stage -/

namespace Host

variable {H : Host}

/-- The domain of a finite set of pairs is finite. -/
theorem fin_dom {θ : H.W} (hθ : H.Fin θ) : H.Fin (H.dom θ) := by
  have key := H.fin_ind (fun x => ∃ D, H.Fin D ∧ ∀ a, a ∈ D ↔ ∃ b, H.App x a b) (by hdef)
    ⟨H.emp, H.fin_emp, fun a => ⟨fun h => (H.not_mem_emp a h).elim,
      fun ⟨b, hb⟩ => (H.not_mem_emp _ (H.app_iff.mp hb)).elim⟩⟩
    (fun x q _ ⟨D, hD, hDm⟩ => by
      by_cases hq : ∃ a b, q = H.op a b
      · obtain ⟨a, b, e⟩ := hq
        refine ⟨H.bun D (H.sg a), H.fin_ins hD a, fun a' => ?_⟩
        rw [H.mem_bun, H.mem_sg, hDm a']
        constructor
        · rintro (⟨b', hb'⟩ | e')
          · exact ⟨b', H.app_iff.mpr (H.mem_bun.mpr (Or.inl (H.app_iff.mp hb')))⟩
          · exact ⟨b, H.app_iff.mpr (H.mem_bun.mpr (Or.inr (H.mem_sg.mpr (by rw [e', e]))))⟩
        · rintro ⟨b', hb'⟩
          rcases H.mem_bun.mp (H.app_iff.mp hb') with h | h
          · exact Or.inl ⟨b', H.app_iff.mpr h⟩
          · exact Or.inr (H.op_inj ((H.mem_sg.mp h).trans e)).1
      · refine ⟨D, hD, fun a' => ?_⟩
        rw [hDm a']
        constructor
        · rintro ⟨b', hb'⟩
          exact ⟨b', H.app_iff.mpr (H.mem_bun.mpr (Or.inl (H.app_iff.mp hb')))⟩
        · rintro ⟨b', hb'⟩
          rcases H.mem_bun.mp (H.app_iff.mp hb') with h | h
          · exact ⟨b', H.app_iff.mpr h⟩
          · exact (hq ⟨a', b', (H.mem_sg.mp h).symm⟩).elim) θ hθ
  obtain ⟨D, hD, hDm⟩ := key
  have e : D = H.dom θ := H.ext' fun a => (hDm a).trans H.mem_dom.symm
  rw [← e]
  exact hD

theorem funOn_comp {π S n : H.W} (hπ : H.IsFun π) (hS : H.FunOn S n)
    (htot : ∀ j v, H.App S j v → ∃ w, H.App π v w) : H.FunOn (H.comp π S) n := by
  refine ⟨⟨comp_pairs π S, fun a b b' h h' => ?_⟩, fun i => ?_⟩
  · obtain ⟨z, hz1, hz2⟩ := app_comp.mp h
    obtain ⟨z', hz1', hz2'⟩ := app_comp.mp h'
    rw [hS.1.2 _ _ _ hz1 hz1'] at hz2
    exact hπ.2 _ _ _ hz2 hz2'
  · rw [hS.2 i]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨w, hw⟩ := htot i z hz
      exact ⟨w, app_comp.mpr ⟨z, hz, hw⟩⟩
    · rintro ⟨w, hw⟩
      obtain ⟨z, hz, -⟩ := app_comp.mp hw
      exact ⟨z, hz⟩

theorem der_fun {π α β ρ : H.W} (hπ : H.IsFun π) (hρ : H.IsDer π α β ρ) : H.IsFun ρ := by
  refine ⟨fun q hq => ?_, fun a b b' hb hb' => ?_⟩
  · obtain ⟨t, u, t', e, -⟩ := (hρ q).mp hq
    exact ⟨_, _, H.isOp_iff.mpr e⟩
  · obtain ⟨t, u, t', e1, e2, hu, hp⟩ := (der_app hρ).mp hb
    obtain ⟨t2, u2, t2', e1', e2', hu', hp'⟩ := (der_app hρ).mp hb'
    obtain ⟨e3, e4⟩ := H.op_inj (e1.symm.trans e1')
    rw [← e3, ← e4] at hp'
    rw [e2, e2', ← e4, (H.op_inj (hπ.2 _ _ _ hp hp')).1]

namespace Tower

variable (T : Tower H)

theorem lev_ex {α : H.W} (hα : T.Proper α) : ∃ La, H.App T.Λ α La ∧ H.Closed La :=
  T.lev α (H.mem_suc.mpr (Or.inl hα.1)) hα.2

theorem lev_closed {α La : H.W} (hα : T.Proper α) (hLa : H.App T.Λ α La) : H.Closed La := by
  obtain ⟨La', hLa', hcl⟩ := T.lev_ex hα
  rw [T.hΛ.2 _ _ _ hLa hLa']
  exact hcl

theorem lev_sub_M {α La : H.W} (hα : T.Proper α) (hLa : H.App T.Λ α La) : H.Sub La T.M := by
  have hd0 : T.d ≠ H.emp := fun e => by
    have h := hα.1
    rw [e] at h
    exact (H.mem_suc.mp h).elim (fun h => H.not_mem_emp _ h) hα.2
  rcases H.mem_suc.mp hα.1 with h | h
  · exact fun z hz => T.hM.trans _ _ hz (T.mono _ _ _ _ hLa (T.hMd hd0) h)
  · rw [h] at hLa
    rw [T.hΛ.2 _ _ _ hLa (T.hMd hd0)]
    exact fun z hz => hz

/-- The ladder is increasing. -/
theorem lev_mono_sub {β α Lb La : H.W} (hαo : α ∈ H.om) (hLb : H.App T.Λ (H.suc β) Lb)
    (hLa : H.App T.Λ α La) (hLacl : H.Closed La) (hβα : β ∈ α) : H.Sub Lb La := by
  rcases H.suc_mem_or α hαo β hβα with h | h
  · exact fun z hz => hLacl.trans _ _ hz (T.mono _ _ _ _ hLb hLa h)
  · rw [h] at hLb
    rw [T.hΛ.2 _ _ _ hLb hLa]
    exact fun z hz => hz

section stage

variable {α : H.W} (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

/-- The names of the codes that are used at the stage `α` are elements of `Λ(α)`. -/
theorem desc_name_La {γ c S La : H.W} (hLa : H.App T.Λ α La)
    (h : H.Desc T.M T.d T.F α γ c S) : c ∈ La := by
  have hcl := T.lev_closed hα hLa
  rcases h with ⟨-, k, i, ec, hk, hi, -⟩ | ⟨h0, hN, -⟩
  · rw [ec]
    exact hcl.op_mem (hcl.nat_mem hk) (hcl.trans _ _ hi (hcl.nat_mem hk))
  · obtain ⟨hγα, hγ⟩ := T.inN_lt hN
    obtain ⟨Lg, hLg, hc⟩ := (hI γ hγα hγ).names c ((T.inN_iff hγ hγα).mp hN)
    exact T.lev_mono_sub (T.proper_om hα) hLg hLa hcl hγα c hc

/-- **Conjugation into the sub-pool.** A partial isomorphism with range bounded in `Λ(α)`
extends to an automorphism that maps a given finite set of tokens into `Λ(α)`. -/
theorem conj_into {La θ R Sp : H.W} (hLa : H.App T.Λ α La) (hθ : H.PIso T.M T.d T.F α θ)
    (hθM : θ ∈ T.M) (hR : R ∈ La) (hRb : ∀ v w, H.App θ v w → w ∈ R) (hfin : H.Fin Sp)
    (htok : ∀ v, v ∈ Sp → H.IsTok T.M T.d α v) :
    ∃ π, H.IsAut T.M T.d T.F α π ∧ H.Sub θ π ∧ ∀ v, v ∈ Sp → ∃ w, w ∈ La ∧ H.App π v w := by
  have hcl := T.lev_closed hα hLa
  obtain ⟨θ', R', hθ', hsub, hR', hR'b, hcov, -, hM', -⟩ :=
    cover (Z := H.emp) T.hM T.hdM hcl (T.lev_sub_M hα hLa) (hcl.nat_mem (H.suc_mem_om T.hd))
      T.hM T.hdM hcl.emp_mem (T.proper_om hα)
      (fun v γ δ c S P _ _ hc => by
        obtain ⟨p, X, η, -, -, -, -, -, -, hdesc⟩ := hc
        exact T.desc_name_La hα hI hLa hdesc) Sp hfin
      (fun v hv => ⟨htok v hv, tok_mem T.hM T.hdM (htok v hv)⟩) θ R hθ hR hRb
  obtain ⟨π, hπ, hsubπ, -⟩ := foa T.hM T.hdM (T.proper_om hα) hθ' (hM' hθM)
  refine ⟨π, hπ, fun q hq => hsubπ q (hsub q hq), fun v hv => ?_⟩
  obtain ⟨w, hw⟩ := hcov v hv
  exact ⟨w, hcl.trans _ _ (hR'b v w hw) hR', H.app_iff.mpr (hsubπ _ (H.app_iff.mp hw))⟩

/-- **Equivariance of the decoding, seen from a stage.** The derivative of an automorphism
maps descriptors to descriptors, and the decoded objects correspond. -/
theorem dec_equi_low {β π ρ c U z : H.W} (hπ : H.IsAut T.M T.d T.F α π) (hβα : β ∈ α)
    (hρ : H.IsDer π α β ρ) (hdesc : H.Desc T.M T.d T.F α β c U)
    (hdec : H.InD T.M T.d T.F α β c U z) :
    ∃ z₂, H.Desc T.M T.d T.F α β c (H.comp ρ U) ∧ H.InD T.M T.d T.F α β c (H.comp ρ U) z₂ ∧
      H.ActLow T.F α π β z z₂ := by
  have hρf := der_fun hπ.1.1 hρ
  by_cases hβ0 : β = H.emp
  · subst hβ0
    rcases hdesc with ⟨-, k, i, ec, hk, hi, hU, htok⟩ | ⟨h0, -⟩
    · have himg : ∀ j v, H.App U j v → ∃ a a', v = H.op a H.emp ∧ H.IsAtom T.M a' ∧
          H.App π (H.op a (H.sg α)) (H.op a' (H.sg α)) ∧ H.App ρ v (H.op a' H.emp) := by
        intro j v hj
        obtain ⟨a, p, ev, hpath, hty, hk'⟩ := htok j v hj
        have hp : p = H.emp := by
          rcases hty with h | h
          · exact h.1
          · exact ((hpath _ h.1).2 rfl).elim
        have ha : H.IsAtom T.M a := hk'.elim id (fun h => (h.2 hp).elim)
        obtain ⟨w, hw⟩ := hπ.2.1 _ (T.tok_atom_top hα ha)
        obtain ⟨a', e⟩ := piso_mid hπ.1 hw
        rw [e] at hw
        have ha' : H.IsAtom T.M a' :=
          ⟨(T.hM.of_op_mem (tok_mem T.hM T.hdM (hπ.1.2.1 _ _ hw).2)).1,
            (hπ.1.2.2.2.1 _ _ _ _ hw).2.mp ha.2⟩
        refine ⟨a, a', by rw [ev, hp], ha', hw, (der_app hρ).mpr ⟨a, H.emp, a', by rw [ev, hp],
          rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩⟩
        rw [emp_bun]
        exact hw
      have hU₂ : H.FunOn (H.comp ρ U) k := funOn_comp hρf hU (fun j v hj => by
        obtain ⟨a, a', -, -, -, h⟩ := himg j v hj
        exact ⟨_, h⟩)
      have hdesc₂ : H.Desc T.M T.d T.F α H.emp c (H.comp ρ U) :=
        Or.inl ⟨rfl, k, i, ec, hk, hi, hU₂, fun j w hj => by
          obtain ⟨v, hv, hvw⟩ := app_comp.mp hj
          obtain ⟨a, a', -, ha', -, hρa⟩ := himg j v hv
          rw [hρf.2 _ _ _ hvw hρa]
          exact ⟨a', H.emp, rfl, fun y hy => (H.not_mem_emp y hy).elim, Or.inl ⟨rfl, rfl⟩,
            Or.inl ha'⟩⟩
      rcases hdec with ⟨-, -, k', i', ec', hi'⟩ | ⟨h0, -⟩
      · obtain ⟨a, a', ev, -, hπa, hρa⟩ := himg i' _ hi'
        rw [← (H.op_inj ev).1] at hπa
        exact ⟨a', hdesc₂, Or.inl ⟨rfl, hdesc₂, k', i', ec', app_comp.mpr ⟨_, hi', hρa⟩⟩,
          Or.inl ⟨rfl, hπa⟩⟩
      · exact (h0 rfl).elim
    · exact (h0 rfl).elim
  · have hβ := T.lower_proper hα hβα hβ0
    have hρA := der_aut (T.proper_om hα) hα.1 hβα hβ0 hπ hρ
    have hρG := (T.mem_Gs hβ).mpr hρA
    rcases hdesc with ⟨e, -⟩ | ⟨-, hN, ⟨n, hn, hU, htok⟩, S0, pat, ec, ⟨n', hU', hS0, hsig⟩⟩
    · exact (hβ0 e).elim
    · have htot : ∀ j v, H.App U j v → ∃ w, H.App ρ v w := fun j v hj =>
        hρA.2.1 v (htok j v hj)
      have hdesc₂ : H.Desc T.M T.d T.F α β c (H.comp ρ U) :=
        Or.inr ⟨hβ0, hN, ⟨n, hn, funOn_comp hρf hU htot, fun j w hj => by
          obtain ⟨v, hv, hvw⟩ := app_comp.mp hj
          exact (hρA.1.2.1 _ _ hvw).2⟩, S0, pat, ec, n', funOn_comp hρf hU' htot, hS0,
          fun j t p t0 p0 hj hj0 => by
            obtain ⟨v, hv, hvw⟩ := app_comp.mp hj
            obtain ⟨t1, e1⟩ := piso_mid' hρA.1 hvw
            rw [e1] at hv hvw
            obtain ⟨h1, h2⟩ := hsig j t1 p t0 p0 hv hj0
            exact ⟨h1, (hρA.1.2.2.2.1 _ _ _ _ hvw).2.symm.trans h2⟩⟩
      have hq := (T.inD_iff hβ hβα).mp hdec
      have hzT := ((hI β hβα hβ).dec_mem c U z hq).1
      obtain ⟨z₂, hz₂, hact⟩ := (hI β hβα hβ).act_tot ρ z hρG hzT
      have hq₂ := (hI β hβα hβ).dec_equi ρ c U (H.comp ρ U) z z₂ hρG hq
        ((desc_stage (β := H.suc β) (H.mem_suc.mpr (Or.inr rfl)) hβα).mpr hdesc₂)
        (fun j v hj => by
          obtain ⟨w, hw⟩ := htot j v hj
          exact ⟨w, app_comp.mpr ⟨v, hj, hw⟩, hw⟩) hact
      exact ⟨z₂, hdesc₂, (T.inD_iff hβ hβα).mpr hq₂,
        (T.low_proper hα (hI β hβα hβ) hβα hβ0 hπ hρ).mpr ⟨hzT, hact⟩⟩

end stage

end Tower

end Host


/-! ## Patterns determine objects; the names of a stage -/

namespace Host

variable {H : Host}

namespace Tower

variable (T : Tower H)

theorem mem_Ns {α c : H.W} (hα : T.Proper α) :
    c ∈ T.Ns α ↔ c ∈ T.Mp ∧ H.IsName T.M T.d T.Λ T.F (T.Tp α) (T.Gs α) α c :=
  (T.spec hα).2.2.2.2.1 c

theorem mem_Ds {α q : H.W} (hα : T.Proper α) :
    q ∈ T.Ds α ↔ q ∈ T.Mp ∧ ∃ c S y, q = H.op c (H.op S y) ∧
      H.IsDec T.M T.d T.Λ T.F (T.Tp α) (T.Gs α) (T.Ns α) α c S y :=
  (T.spec hα).2.2.2.2.2 q

theorem emp_mem_Tp {α : H.W} (hα : T.Proper α) : H.op H.emp H.emp ∈ T.Tp α :=
  ((T.spec hα).2.2.1 _).mpr ⟨T.hMp.op_mem T.hMp.emp_mem T.hMp.emp_mem, H.emp, H.emp, rfl,
    Or.inl ⟨rfl, rfl⟩, H.emp, H.fin_emp, fun v hv => (H.not_mem_emp v hv).elim,
    fun _ _ _ => actRaw_emp⟩

section stage

variable {α : H.W} (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

omit hI in
theorem next_sub_Mp {L' : H.W} (hL' : H.App T.Λ (H.suc α) L') : H.Sub L' T.Mp := by
  rcases H.suc_mem_or _ (H.suc_mem_om T.hd) _ hα.1 with h | h
  · exact fun z hz => T.hMp.trans _ _ hz (T.mono _ _ _ _ hL' T.hMpd h)
  · rw [h] at hL'
    rw [T.hΛ.2 _ _ _ hL' T.hMpd]
    exact fun z hz => hz

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **One half of the injectivity of patterns.** If two pre-objects with the same lower level
are supported by a tuple of the sub-pool, and every descriptor over the sub-pool that decodes
into the first decodes into the second, then the first is included in the second. -/
theorem pat_sub {La S0 β D D' : H.W} (hLa : H.App T.Λ α La) (hS0 : H.IsTup T.M T.d α S0)
    (hS0L : S0 ∈ La) (hβα : β ∈ α) (hD : ∀ z, z ∈ D → z ∈ T.Ts β)
    (hD' : ∀ z, z ∈ D' → z ∈ T.Ts β)
    (hsx : H.SuppTup T.F (T.Gs α) α S0 (H.op β D))
    (hsx' : H.SuppTup T.F (T.Gs α) α S0 (H.op β D'))
    (hpat : ∀ c U z, U ∈ La → H.Desc T.M T.d T.F α β c U → H.InD T.M T.d T.F α β c U z →
      z ∈ D → z ∈ D') : H.Sub D D' := by
  intro z hz
  have hcl := T.lev_closed hα hLa
  have hLM := T.lev_sub_M hα hLa
  have hαo := T.proper_om hα
  have hdL : H.suc T.d ∈ La := hcl.nat_mem (H.suc_mem_om T.hd)
  obtain ⟨c, U, hdesc, hdec⟩ := T.ex_desc hα hI hβα (hD z hz)
  obtain ⟨n0, hn0, hS0f, hS0t⟩ := hS0
  have hS0e : ∀ j v, H.App S0 j v → v ∈ La := fun j v hj =>
    (hcl.of_op_mem (hcl.trans _ _ (H.app_iff.mp hj) hS0L)).2
  have hnm : ∀ v γ δ c S P, v ∈ La → H.IsTok T.M T.d α v →
      H.Col T.M T.d T.F α v γ δ c S P → c ∈ La := fun v γ δ c S P _ _ hc => by
    obtain ⟨p, X, η, -, -, -, -, -, -, hdesc⟩ := hc
    exact T.desc_name_La hα hI hLa hdesc
  -- a closed set of tokens of the sub-pool that contains the entries of `S0`
  obtain ⟨θ1, R1, hθ1, -, -, -, hcov1, hnew1, -, hF1⟩ :=
    cover (Z := H.emp) T.hM T.hdM hcl hLM hdL hcl hdL hcl.emp_mem hαo hnm
      (H.ran S0) ⟨n0, S0, hn0, hS0f, fun z => H.mem_ran⟩
      (fun v hv => by
        obtain ⟨j, hj⟩ := H.mem_ran.mp hv
        exact ⟨hS0t j v hj, hS0e j v hj⟩)
      H.emp H.emp piso_emp hcl.emp_mem (fun v w h => (H.not_mem_emp _ (H.app_iff.mp h)).elim)
  have hdomL : H.dom θ1 ∈ La := hcl.fin_mem (fin_dom (hF1 H.fin_emp)) (fun v hv => by
    obtain ⟨w, hw⟩ := H.mem_dom.mp hv
    rcases hnew1 v w hw with h | h
    · exact (H.not_mem_emp _ (H.app_iff.mp h)).elim
    · exact h.1)
  -- the entries of `U`, raised to the stage
  obtain ⟨nU, hnU, hUf⟩ := desc_fun hdesc
  have hR : Def2 H (fun v w => ∃ t u, v = H.op t u ∧ w = H.op t (H.bun u (H.sg α))) := by hdef
  have hRf : ∀ v ∈ H.ran U, ∀ w w', (∃ t u, v = H.op t u ∧ w = H.op t (H.bun u (H.sg α))) →
      (∃ t u, v = H.op t u ∧ w' = H.op t (H.bun u (H.sg α))) → w = w' := by
    rintro v - w w' ⟨t, u, e, ew⟩ ⟨t', u', e', ew'⟩
    obtain ⟨e1, e2⟩ := H.op_inj (e.symm.trans e')
    rw [ew, ew', e1, e2]
  obtain ⟨r, hrf, hr⟩ : ∃ r, H.IsFun r ∧ ∀ v w, H.App r v w ↔
      v ∈ H.ran U ∧ ∃ t u, v = H.op t u ∧ w = H.op t (H.bun u (H.sg α)) :=
    ⟨H.mkFun (H.ran U) _ hR hRf, H.isFun_mkFun, fun v w => H.app_mkFun⟩
  obtain ⟨SpU, hSpUfin, hSpU⟩ := fin_image
    (⟨nU, U, hnU, hUf, fun z => H.mem_ran⟩ : H.Fin (H.ran U)) hrf (fun v hv => by
      obtain ⟨j, hj⟩ := H.mem_ran.mp hv
      obtain ⟨t, u, e, -⟩ := desc_tok hdesc hj
      exact ⟨_, (hr _ _).mpr ⟨hv, t, u, e, rfl⟩⟩)
  have hSpUmem : ∀ j t u, H.App U j (H.op t u) → H.op t (H.bun u (H.sg α)) ∈ SpU :=
    fun j t u hj => (hSpU _).mpr ⟨_, H.mem_ran.mpr ⟨j, hj⟩,
      (hr _ _).mpr ⟨H.mem_ran.mpr ⟨j, hj⟩, t, u, rfl, rfl⟩⟩
  -- an automorphism that fixes the entries of `S0` and maps the raised entries into `La`
  obtain ⟨π, hπ, hsubπ, hπL⟩ := T.conj_into hα hI hLa (piso_id_dom hθ1)
    (T.hM.idOn_mem (hLM _ hdomL)) hdomL
    (fun v w h => by
      obtain ⟨hv, e⟩ := app_idOn.mp h
      rw [e]
      exact hv) hSpUfin
    (fun w hw => by
      obtain ⟨v, hv, hvw⟩ := (hSpU w).mp hw
      obtain ⟨-, t, u, e, ew⟩ := (hr _ _).mp hvw
      obtain ⟨j, hj⟩ := H.mem_ran.mp hv
      rw [ew]
      have htk := desc_tok hdesc hj
      rw [e] at htk
      exact tok_raise hαo hβα hα.1 htk)
  have hπG := (T.mem_Gs hα).mpr hπ
  have hfix : ∀ j v, H.App S0 j v → H.App π v v := fun j v hj => by
    obtain ⟨w, hw⟩ := hcov1 v (H.mem_ran.mpr ⟨j, hj⟩)
    exact H.app_iff.mpr (hsubπ _ (H.app_iff.mp (app_idOn.mpr ⟨H.mem_dom.mpr ⟨w, hw⟩, rfl⟩)))
  obtain ⟨ρ, hρ, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hπ.1) α β
  obtain ⟨z₂, hdesc₂, hdec₂, hact⟩ := T.dec_equi_low hα hI hπ hβα hρ hdesc hdec
  have hz₂ : z₂ ∈ D := by
    obtain ⟨β1, D1, D1', e1, e2, hD1⟩ := hsx π hπG hfix
    obtain ⟨e3, e4⟩ := H.op_inj e1
    obtain ⟨-, e4'⟩ := H.op_inj e2
    rw [← e3, ← e4] at hD1
    rw [e4']
    exact (hD1 z₂).mpr ⟨z, hz, hact⟩
  have hU₂L : H.comp ρ U ∈ La := by
    obtain ⟨n2, hn2, hU₂f⟩ := desc_fun hdesc₂
    refine hcl.fun_mem hU₂f (hcl.nat_mem hn2) (fun j w hj => ?_)
    obtain ⟨v, hv, hvw⟩ := app_comp.mp hj
    obtain ⟨t, u, t', ev, ew, -, hπt⟩ := (der_app hρ).mp hvw
    rw [ev] at hv
    obtain ⟨w0, hw0L, hw0⟩ := hπL _ (hSpUmem j t u hv)
    rw [hπ.1.1.2 _ _ _ hw0 hπt] at hw0L
    obtain ⟨ht', hp'⟩ := hcl.of_op_mem hw0L
    rw [ew]
    exact hcl.op_mem ht' (hcl.sub u _ (fun x hx => H.mem_bun.mpr (Or.inl hx)) hp')
  have hz₂' : z₂ ∈ D' := hpat c (H.comp ρ U) z₂ hU₂L hdesc₂ hdec₂ hz₂
  obtain ⟨β1, D1, D1', e1, e2, hD1⟩ := hsx' π hπG hfix
  obtain ⟨e3, e4⟩ := H.op_inj e1
  obtain ⟨-, e4'⟩ := H.op_inj e2
  rw [← e3, ← e4] at hD1
  rw [e4'] at hz₂'
  obtain ⟨z0, hz0, hact0⟩ := (hD1 z₂).mp hz₂'
  have h1 := T.low_inv hα hI hπ hβα (hD' z0 hz0) hact0
  have h2 := T.low_inv hα hI hπ hβα (hD z hz) hact
  rw [T.low_fun (isAut_inv hπ).1.1 h2 h1]
  exact hz0

/-- **Patterns are injective.** Two objects that are supported by the same tuple of the
sub-pool and have the same pattern are equal. -/
theorem pat_inj {La S0 pat x x' : H.W} (hLa : H.App T.Λ α La) (hS0 : H.IsTup T.M T.d α S0)
    (hS0L : S0 ∈ La) (hx : x ∈ T.Tp α) (hx' : x' ∈ T.Tp α)
    (hsx : H.SuppTup T.F (T.Gs α) α S0 x) (hsx' : H.SuppTup T.F (T.Gs α) α S0 x')
    (hp : H.IsPat T.M T.d T.F α La x pat) (hp' : H.IsPat T.M T.d T.F α La x' pat) : x = x' := by
  obtain ⟨β, D, P0, ex, ep, hP0⟩ := hp
  obtain ⟨β', D', P0', ex', ep', hP0'⟩ := hp'
  obtain ⟨eβ, eP⟩ := H.op_inj (ep.symm.trans ep')
  rw [← eβ] at ex' hP0'
  rw [← eP] at hP0'
  obtain ⟨γ, D1, e1, hγα, hD1⟩ := T.obj_pre hα hx
  obtain ⟨e2, e3⟩ := H.op_inj (ex.symm.trans e1)
  rw [← e2] at hγα hD1
  rw [← e3] at hD1
  obtain ⟨γ', D1', e1', -, hD1'⟩ := T.obj_pre hα hx'
  obtain ⟨e2', e3'⟩ := H.op_inj (ex'.symm.trans e1')
  rw [← e2'] at hD1'
  rw [← e3'] at hD1'
  rw [ex] at hsx
  rw [ex'] at hsx'
  have h1 : H.Sub D D' := T.pat_sub hα hI hLa hS0 hS0L hγα hD1 hD1' hsx hsx'
    (fun c U z hU hdesc hdec hz => by
      obtain ⟨c2, U2, z2, e, -, -, hdec2, hz2⟩ :=
        (hP0' _).mp ((hP0 _).mpr ⟨c, U, z, rfl, hU, hdesc, hdec, hz⟩)
      obtain ⟨ec, eU⟩ := H.op_inj e
      rw [← ec, ← eU] at hdec2
      rw [T.inD_fun hα hI hγα hdec hdec2]
      exact hz2)
  have h2 : H.Sub D' D := T.pat_sub hα hI hLa hS0 hS0L hγα hD1' hD1 hsx' hsx
    (fun c U z hU hdesc hdec hz => by
      obtain ⟨c2, U2, z2, e, -, -, hdec2, hz2⟩ :=
        (hP0 _).mp ((hP0' _).mpr ⟨c, U, z, rfl, hU, hdesc, hdec, hz⟩)
      obtain ⟨ec, eU⟩ := H.op_inj e
      rw [← ec, ← eU] at hdec2
      rw [T.inD_fun hα hI hγα hdec hdec2]
      exact hz2)
  rw [ex, ex', H.sub_antisymm h1 h2]

/-- A name of the stage `α` is an element of the next level of the ladder. -/
theorem isName_mem {c : H.W} (h : H.IsName T.M T.d T.Λ T.F (T.Tp α) (T.Gs α) α c) :
    ∃ L', H.App T.Λ (H.suc α) L' ∧ H.Closed L' ∧ c ∈ L' := by
  obtain ⟨S0, pat, x, La, ec, hLa, hS0L, -, hx, -, β, D, P0, ex, ep, hP0⟩ := h
  have hcl := T.lev_closed hα hLa
  have hsα : H.suc α ∈ H.suc (H.suc T.d) :=
    (H.suc_mem_or _ (H.suc_mem_om T.hd) _ hα.1).elim (fun h => H.mem_suc.mpr (Or.inl h))
      (fun h => H.mem_suc.mpr (Or.inr h))
  obtain ⟨L', hL', hcl'⟩ := T.lev (H.suc α) hsα (H.suc_ne_emp α)
  have hLL : La ∈ L' := T.mono _ _ _ _ hLa hL' (H.mem_suc.mpr (Or.inr rfl))
  refine ⟨L', hL', hcl', ?_⟩
  obtain ⟨γ, D1, e1, hγα, -⟩ := T.obj_pre hα hx
  have hβL : β ∈ L' := by
    rw [(H.op_inj (ex.symm.trans e1)).1]
    exact hcl'.nat_mem (H.om_trans _ (T.proper_om hα) γ hγα).1
  have hP0L : P0 ∈ L' := hcl'.sub _ _ (fun e he => by
    obtain ⟨c', U, z, ee, hU, hdesc, -⟩ := (hP0 e).mp he
    rw [ee]
    exact hcl.op_mem (T.desc_name_La hα hI hLa hdesc) hU) hLL
  rw [ec, ep]
  exact hcl'.op_mem (hcl'.trans _ _ hS0L hLL) (hcl'.op_mem hβL hP0L)

theorem names_stage {c : H.W} (hc : c ∈ T.Ns α) : ∃ L', H.App T.Λ (H.suc α) L' ∧ c ∈ L' := by
  obtain ⟨L', h1, -, h2⟩ := T.isName_mem hα hI ((T.mem_Ns hα).mp hc).2
  exact ⟨L', h1, h2⟩

end stage

end Tower

end Host


/-! ## The decoding of a stage; the invariants of a stage from those of the lower stages -/

namespace Host

variable {H : Host}

theorem sameSig_ex {S S0 j v : H.W} (h : H.SameSig S S0) (hj : H.App S0 j v) :
    ∃ w, H.App S j w := by
  obtain ⟨n, hS, hS0, -⟩ := h
  exact (hS.2 j).mp ((hS0.2 j).mpr ⟨v, hj⟩)

namespace Tower

variable (T : Tower H)

section stage

variable {α : H.W} (hα : T.Proper α) (hI : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ)
include hα hI

/-- Membership of a triple in the decoding of the stage. -/
theorem dec_iff {c S y : H.W} : H.op c (H.op S y) ∈ T.Ds α ↔
    H.IsDec T.M T.d T.Λ T.F (T.Tp α) (T.Gs α) (T.Ns α) α c S y := by
  rw [T.mem_Ds hα]
  constructor
  · rintro ⟨-, c', S', y', e, h⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e3, e4⟩ := H.op_inj e2
    rw [e1, e3, e4]
    exact h
  · intro h
    refine ⟨?_, c, S, y, rfl, h⟩
    obtain ⟨hc, hS, S0, pat, x, La, -, -, -, hx, -, -, hy⟩ := h
    refine T.hMp.op_mem ((T.mem_Ns hα).mp hc).1 (T.hMp.op_mem (T.M_sub_Mp (T.tup_mem_M hS)) ?_)
    rcases hy with ⟨π, hπG, -, hact⟩ | ⟨-, e⟩
    · obtain ⟨y', hy', hact'⟩ := T.act_tot_stage hα hI hπG hx
      rw [actRaw_fun hact hact']
      exact T.Tp_sub hα hy'
    · rw [e]
      exact T.hMp.op_mem T.hMp.emp_mem T.hMp.emp_mem

omit hI in
theorem name_data {c S0 pat : H.W} (hc : c ∈ T.Ns α) (ec : c = H.op S0 pat) :
    ∃ x La, H.App T.Λ α La ∧ S0 ∈ La ∧ H.IsTup T.M T.d α S0 ∧ x ∈ T.Tp α ∧
      H.SuppTup T.F (T.Gs α) α S0 x ∧ H.IsPat T.M T.d T.F α La x pat := by
  obtain ⟨S0', pat', x, La, ec', h⟩ := ((T.mem_Ns hα).mp hc).2
  obtain ⟨e1, e2⟩ := H.op_inj (ec.symm.trans ec')
  rw [e1, e2]
  exact ⟨x, La, h⟩

theorem dec_tot_stage {c S : H.W} (hdesc : H.Desc T.M T.d T.F (H.suc α) α c S) :
    ∃ y, H.op c (H.op S y) ∈ T.Ds α := by
  have hsuc : α ∈ H.suc α := H.mem_suc.mpr (Or.inr rfl)
  rcases hdesc with ⟨e, -⟩ | ⟨-, hN, hS, S0, pat, ec, hsig⟩
  · exact (hα.2 e).elim
  · have hc := (T.inN_iff hα hsuc).mp hN
    obtain ⟨x, La, hLa, -, -, hx, hsupp, hpat⟩ := T.name_data hα hc ec
    by_cases h : ∃ π, π ∈ T.Gs α ∧ H.MapsTup π S0 S
    · obtain ⟨π, hπG, hmaps⟩ := h
      obtain ⟨y, -, hact⟩ := T.act_tot_stage hα hI hπG hx
      exact ⟨y, (T.dec_iff hα hI).mpr ⟨hc, hS, S0, pat, x, La, ec, hsig, hLa, hx, hsupp, hpat,
        Or.inl ⟨π, hπG, hmaps, hact⟩⟩⟩
    · exact ⟨_, (T.dec_iff hα hI).mpr ⟨hc, hS, S0, pat, x, La, ec, hsig, hLa, hx, hsupp, hpat,
        Or.inr ⟨h, rfl⟩⟩⟩

theorem dec_mem_stage {c S y : H.W} (hq : H.op c (H.op S y) ∈ T.Ds α) :
    y ∈ T.Tp α ∧ H.Desc T.M T.d T.F (H.suc α) α c S := by
  obtain ⟨hc, hS, S0, pat, x, La, ec, hsig, hLa, hx, hsupp, hpat, hy⟩ := (T.dec_iff hα hI).mp hq
  refine ⟨?_, Or.inr ⟨hα.2, (T.inN_iff hα (H.mem_suc.mpr (Or.inr rfl))).mpr hc, hS, S0, pat, ec,
    hsig⟩⟩
  rcases hy with ⟨π, hπG, -, hact⟩ | ⟨-, e⟩
  · obtain ⟨y', hy', hact'⟩ := T.act_tot_stage hα hI hπG hx
    rw [actRaw_fun hact hact']
    exact hy'
  · rw [e]
    exact T.emp_mem_Tp hα

theorem dec_fun_stage {c S y y' : H.W} (hq : H.op c (H.op S y) ∈ T.Ds α)
    (hq' : H.op c (H.op S y') ∈ T.Ds α) : y = y' := by
  obtain ⟨hc, hS, S0, pat, x, La, ec, hsig, hLa, hx, hsupp, hpat, hy⟩ := (T.dec_iff hα hI).mp hq
  obtain ⟨-, -, S0', pat', x', La', ec', -, hLa', hx', hsupp', hpat', hy'⟩ :=
    (T.dec_iff hα hI).mp hq'
  obtain ⟨e1, e2⟩ := H.op_inj (ec'.symm.trans ec)
  rw [e1] at hsupp' hy'
  rw [e2, T.hΛ.2 _ _ _ hLa' hLa] at hpat'
  obtain ⟨x0, La0, hLa0, hS0L, hS0, -⟩ := T.name_data hα hc ec
  rw [T.hΛ.2 _ _ _ hLa0 hLa] at hS0L
  have ex : x' = x := T.pat_inj hα hI hLa hS0 hS0L hx' hx hsupp' hsupp hpat' hpat
  rw [ex] at hy'
  rcases hy with ⟨π, hπG, hmaps, hact⟩ | ⟨hno, e⟩
  · rcases hy' with ⟨π', hπ'G, hmaps', hact'⟩ | ⟨hno', -⟩
    · have hπ := (T.mem_Gs hα).mp hπG
      have hπ' := (T.mem_Gs hα).mp hπ'G
      have hxpre := T.obj_pre hα hx
      have hκ : H.ActRaw T.F α (H.comp (H.inv π') π) x x :=
        hsupp _ ((T.mem_Gs hα).mpr (isAut_comp hπ (isAut_inv hπ'))) (fun j v hj => by
          obtain ⟨w, hw⟩ := sameSig_ex hsig hj
          exact app_comp.mpr ⟨w, hmaps j v w hj hw, app_inv.mpr (hmaps' j v w hj hw)⟩)
      have hypre := T.raw_pre hα hI hπ hxpre hact
      obtain ⟨x₂, -, hact₂⟩ := T.raw_tot hα hI (isAut_inv hπ') hypre
      have e := actRaw_fun (T.raw_comp hα hI hπ (isAut_inv hπ') hxpre hact hact₂) hκ
      rw [e] at hact₂
      have h3 := T.raw_inv hα hI (isAut_inv hπ') hypre hact₂
      rw [inv_inv hπ'.1.1.1] at h3
      exact actRaw_fun h3 hact'
    · exact (hno' ⟨π, hπG, hmaps⟩).elim
  · rcases hy' with ⟨π', hπ'G, hmaps', -⟩ | ⟨-, e'⟩
    · exact (hno ⟨π', hπ'G, hmaps'⟩).elim
    · rw [e, e']

theorem dec_supp_stage {c S y : H.W} (hq : H.op c (H.op S y) ∈ T.Ds α) :
    H.SuppTup T.F (T.Gs α) α S y := by
  obtain ⟨hc, hS, S0, pat, x, La, ec, hsig, hLa, hx, hsupp, hpat, hy⟩ := (T.dec_iff hα hI).mp hq
  rcases hy with ⟨π, hπG, hmaps, hact⟩ | ⟨-, e⟩
  · have hπ := (T.mem_Gs hα).mp hπG
    have h1 : H.SuppSet T.F (T.Gs α) α (H.ran S0) x := fun σ hσ hfix =>
      hsupp σ hσ (fun j v hj => hfix v (H.mem_ran.mpr ⟨j, hj⟩))
    have h2 := T.supp_conj hα hI hπ (T.obj_pre hα hx) hact h1 (Sp' := H.ran S) (fun v hv => by
      obtain ⟨j, hj⟩ := H.mem_ran.mp hv
      obtain ⟨w, hw⟩ := sameSig_ex hsig hj
      exact ⟨w, H.mem_ran.mpr ⟨j, hw⟩, hmaps j v w hj hw⟩)
    exact fun σ hσ hfix => h2 σ hσ (fun v hv => by
      obtain ⟨j, hj⟩ := H.mem_ran.mp hv
      exact hfix j v hj)
  · rw [e]
    exact fun σ _ _ => actRaw_emp

theorem dec_equi_stage {π c S S' y y' : H.W} (hπG : π ∈ T.Gs α)
    (hq : H.op c (H.op S y) ∈ T.Ds α) (hdesc' : H.Desc T.M T.d T.F (H.suc α) α c S')
    (hmap : ∀ j v, H.App S j v → ∃ w, H.App S' j w ∧ H.App π v w)
    (hact : H.ActRaw T.F α π y y') : H.op c (H.op S' y') ∈ T.Ds α := by
  have hπ := (T.mem_Gs hα).mp hπG
  obtain ⟨hc, hS, S0, pat, x, La, ec, hsig, hLa, hx, hsupp, hpat, hy⟩ := (T.dec_iff hα hI).mp hq
  rcases hdesc' with ⟨e, -⟩ | ⟨-, -, hS', S0', pat', ec', hsig'⟩
  · exact (hα.2 e).elim
  · obtain ⟨e1, -⟩ := H.op_inj (ec'.symm.trans ec)
    rw [e1] at hsig'
    have hS'f : ∀ j w w', H.App S' j w → H.App S' j w' → w = w' := by
      obtain ⟨n, hn, -⟩ := id hsig'
      exact fun j w w' h h' => hn.1.2 _ _ _ h h'
    refine (T.dec_iff hα hI).mpr ⟨hc, hS', S0, pat, x, La, ec, hsig', hLa, hx, hsupp, hpat, ?_⟩
    rcases hy with ⟨σ, hσG, hmaps, hactσ⟩ | ⟨hno, e⟩
    · have hσ := (T.mem_Gs hα).mp hσG
      refine Or.inl ⟨H.comp π σ, (T.mem_Gs hα).mpr (isAut_comp hσ hπ),
        fun j v w' hj hj' => ?_, T.raw_comp hα hI hσ hπ (T.obj_pre hα hx) hactσ hact⟩
      obtain ⟨w, hw⟩ := sameSig_ex hsig hj
      obtain ⟨w'', hw'', hπw⟩ := hmap j w hw
      rw [hS'f j w' w'' hj' hw'']
      exact app_comp.mpr ⟨w, hmaps j v w hj hw, hπw⟩
    · rw [e] at hact
      refine Or.inr ⟨fun ⟨σ', hσ'G, hmaps'⟩ => hno ⟨H.comp (H.inv π) σ',
        (T.mem_Gs hα).mpr (isAut_comp ((T.mem_Gs hα).mp hσ'G) (isAut_inv hπ)),
        fun j v w hj hjw => ?_⟩, actRaw_fun hact actRaw_emp⟩
      obtain ⟨w', hw', hπw⟩ := hmap j w hjw
      exact app_comp.mpr ⟨w', hmaps' j v w' hj hw', app_inv.mpr hπw⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **Every object has a descriptor.** An object is conjugate to an object that is supported
by a tuple of the sub-pool; the name is that tuple together with the pattern. -/
theorem dec_surj_stage {x : H.W} (hx : x ∈ T.Tp α) : ∃ c S, H.op c (H.op S x) ∈ T.Ds α := by
  obtain ⟨-, β0, D0, -, -, Sp, hfin, htok, hsupp⟩ := ((T.spec hα).2.2.1 x).mp hx
  obtain ⟨La, hLa, hcl⟩ := T.lev_ex hα
  obtain ⟨π, hπ, -, hπL⟩ := T.conj_into hα hI hLa piso_emp T.hM.emp_mem hcl.emp_mem
    (fun v w h => (H.not_mem_emp _ (H.app_iff.mp h)).elim) hfin htok
  have hπG := (T.mem_Gs hα).mpr hπ
  have hxpre := T.obj_pre hα hx
  obtain ⟨x', hx', hact⟩ := T.act_tot_stage hα hI hπG hx
  obtain ⟨Sp', hfin', hSp'⟩ := fin_image hfin hπ.1.1 (fun v hv => hπ.2.1 v (htok v hv))
  have hsupp' : H.SuppSet T.F (T.Gs α) α Sp' x' :=
    T.supp_conj hα hI hπ hxpre hact hsupp (fun v hv => by
      obtain ⟨w, hw⟩ := hπ.2.1 v (htok v hv)
      exact ⟨w, (hSp' w).mpr ⟨v, hv, hw⟩, hw⟩)
  obtain ⟨n, S0, hn, hS0f, hS0r⟩ := hfin'
  have hS0t : ∀ j w, H.App S0 j w → H.IsTok T.M T.d α w ∧ w ∈ La := fun j w hj => by
    obtain ⟨v, hv, hvw⟩ := (hSp' w).mp ((hS0r w).mpr ⟨j, hj⟩)
    obtain ⟨w0, hw0L, hw0⟩ := hπL v hv
    rw [hπ.1.1.2 _ _ _ hvw hw0]
    exact ⟨(hπ.1.2.1 _ _ hw0).2, hw0L⟩
  have hS0 : H.IsTup T.M T.d α S0 := ⟨n, hn, hS0f, fun j w hj => (hS0t j w hj).1⟩
  have hS0L : S0 ∈ La := hcl.fun_mem hS0f (hcl.nat_mem hn) (fun j w hj => (hS0t j w hj).2)
  have hsuppT : H.SuppTup T.F (T.Gs α) α S0 x' := fun σ hσ hfix =>
    hsupp' σ hσ (fun v hv => by
      obtain ⟨j, hj⟩ := (hS0r v).mp hv
      exact hfix j v hj)
  obtain ⟨β, D, ex', hβα, -⟩ := T.obj_pre hα hx'
  obtain ⟨P0, hP0⟩ := H.sep' La (fun e => ∃ c U z, e = H.op c U ∧ U ∈ La ∧
    H.Desc T.M T.d T.F α β c U ∧ H.InD T.M T.d T.F α β c U z ∧ z ∈ D) (by hdef)
  have hpat : H.IsPat T.M T.d T.F α La x' (H.op β P0) :=
    ⟨β, D, P0, ex', rfl, fun e => ⟨fun h => ((hP0 e).mp h).2, fun h => (hP0 e).mpr ⟨by
      obtain ⟨c, U, z, ee, hU, hdesc, -⟩ := h
      rw [ee]
      exact hcl.op_mem (T.desc_name_La hα hI hLa hdesc) hU, h⟩⟩⟩
  have hname : H.IsName T.M T.d T.Λ T.F (T.Tp α) (T.Gs α) α (H.op S0 (H.op β P0)) :=
    ⟨S0, _, x', La, rfl, hLa, hS0L, hS0, hx', hsuppT, hpat⟩
  have hc : H.op S0 (H.op β P0) ∈ T.Ns α := by
    obtain ⟨L', hL', -, hcL'⟩ := T.isName_mem hα hI hname
    exact (T.mem_Ns hα).mpr ⟨T.next_sub_Mp hα hL' _ hcL', hname⟩
  have hinv := isAut_inv hπ
  have hSf : H.FunOn (H.comp (H.inv π) S0) n :=
    funOn_comp hinv.1.1 hS0f (fun j w hj => hinv.2.1 w (hS0t j w hj).1)
  have hS : H.IsTup T.M T.d α (H.comp (H.inv π) S0) := ⟨n, hn, hSf, fun j v hj => by
    obtain ⟨w, -, hwv⟩ := app_comp.mp hj
    exact (hinv.1.2.1 _ _ hwv).2⟩
  have hsig : H.SameSig (H.comp (H.inv π) S0) S0 := ⟨n, hSf, hS0f, fun j t p t0 p0 hj hj0 => by
    obtain ⟨w, hw, hwv⟩ := app_comp.mp hj
    rw [hS0f.1.2 _ _ _ hw hj0] at hwv
    exact hπ.1.2.2.2.1 _ _ _ _ (app_inv.mp hwv)⟩
  refine ⟨_, H.comp (H.inv π) S0, (T.dec_iff hα hI).mpr ⟨hc, hS, S0, _, x', La, rfl, hsig, hLa,
    hx', hsuppT, hpat, Or.inl ⟨H.inv π, (T.mem_Gs hα).mpr hinv, fun j v w hj hjw => ?_,
      T.raw_inv hα hI hπ hxpre hact⟩⟩⟩
  obtain ⟨v', hv', hv'w⟩ := app_comp.mp hjw
  rw [hS0f.1.2 _ _ _ hj hv']
  exact hv'w

/-- The set of objects of a stage below the top is an element of the object level. -/
theorem tp_mem_stage (hαd : α ∈ T.d) : T.Tp α ∈ T.Mp := by
  obtain ⟨f, hf⟩ := H.sep' (H.prod (H.prod (T.Ns α) T.M) (T.Tp α))
    (fun q => ∃ c S y, q = H.op (H.op c S) y ∧ H.op c (H.op S y) ∈ T.Ds α) (by hdef)
  have happ : ∀ c S y, H.App f (H.op c S) y ↔ H.op c (H.op S y) ∈ T.Ds α := by
    intro c S y
    rw [H.app_iff, hf]
    constructor
    · rintro ⟨-, c', S', y', e, h⟩
      obtain ⟨e1, e2⟩ := H.op_inj e
      obtain ⟨e3, e4⟩ := H.op_inj e1
      rw [e3, e4, e2]
      exact h
    · intro h
      obtain ⟨hc, hS, -⟩ := (T.dec_iff hα hI).mp h
      exact ⟨H.op_mem_prod.mpr ⟨H.op_mem_prod.mpr ⟨hc, T.tup_mem_M hS⟩,
        (T.dec_mem_stage hα hI h).1⟩, c, S, y, rfl, h⟩
  have hfun : H.IsFun f := ⟨fun q hq => by
      obtain ⟨-, c, S, y, e, -⟩ := (hf q).mp hq
      exact ⟨_, _, H.isOp_iff.mpr e⟩, fun a b b' h h' => by
      obtain ⟨-, c, S, y, e, hq⟩ := (hf _).mp (H.app_iff.mp h)
      obtain ⟨e1, e2⟩ := H.op_inj e
      rw [e1] at h h'
      exact T.dec_fun_stage hα hI ((happ c S b).mp h) ((happ c S b').mp h')⟩
  have hsα : H.suc α ∈ H.suc T.d := (H.suc_mem_or _ T.hd _ hαd).elim
    (fun h => H.mem_suc.mpr (Or.inl h)) (fun h => H.mem_suc.mpr (Or.inr h))
  obtain ⟨L', hL', -⟩ := T.lev (H.suc α) (H.mem_suc.mpr (Or.inl hsα)) (H.suc_ne_emp α)
  have hL'Mp : L' ∈ T.Mp := T.mono _ _ _ _ hL' T.hMpd hsα
  have hNMp : T.Ns α ∈ T.Mp := T.hMp.sub _ _ (fun c hc => by
    obtain ⟨L'', hL'', hcL⟩ := T.names_stage hα hI hc
    rw [T.hΛ.2 _ _ _ hL'' hL'] at hcL
    exact hcL) hL'Mp
  have hdom : H.dom f ∈ T.Mp := T.hMp.sub _ _ (fun a ha => by
    obtain ⟨y, hy⟩ := H.mem_dom.mp ha
    obtain ⟨hmem, -⟩ := (hf _).mp (H.app_iff.mp hy)
    exact (H.op_mem_prod.mp hmem).1) (T.hMp.prod_mem hNMp T.hMMp)
  obtain ⟨Y, hY, hYb⟩ := T.hMp.bd f hfun hdom (fun a b hab => by
    obtain ⟨hmem, -⟩ := (hf _).mp (H.app_iff.mp hab)
    exact T.Tp_sub hα (H.op_mem_prod.mp hmem).2)
  refine T.hMp.sub _ Y (fun x hx => ?_) hY
  obtain ⟨c, S, hq⟩ := T.dec_surj_stage hα hI hx
  exact hYb _ x ((happ c S x).mpr hq)

/-- **The step of the induction on levels.** -/
theorem invT_step : T.InvT α where
  act_tot := fun _ _ hπ hx => T.act_tot_stage hα hI hπ hx
  act_comp := fun _ _ _ _ _ hπ hσ hx h h' =>
    T.raw_comp hα hI ((T.mem_Gs hα).mp hπ) ((T.mem_Gs hα).mp hσ) (T.obj_pre hα hx) h h'
  act_inv := fun _ _ _ hπ hx h => T.raw_inv hα hI ((T.mem_Gs hα).mp hπ) (T.obj_pre hα hx) h
  names := fun _ hc => T.names_stage hα hI hc
  dec_tot := fun _ _ h => T.dec_tot_stage hα hI h
  dec_fun := fun _ _ _ _ h h' => T.dec_fun_stage hα hI h h'
  dec_mem := fun _ _ _ h => T.dec_mem_stage hα hI h
  dec_surj := fun _ hx => T.dec_surj_stage hα hI hx
  dec_equi := fun _ _ _ _ _ _ hπ hq hd hm ha => T.dec_equi_stage hα hI hπ hq hd hm ha
  dec_supp := fun _ _ _ h => T.dec_supp_stage hα hI h
  tp_mem := fun h => T.tp_mem_stage hα hI h
  lit := fun _ _ hb hl => T.lit_mem hα hb hl

end stage

end Tower

end Host


/-! ## The induction on levels: every proper level satisfies the invariants -/

namespace Host

variable {H : Host}

/-- `κ` is the composite: first `π`, then `σ`. -/
def IsCompOf (H : Host) (κ σ π : H.W) : Prop :=
  ∀ q, q ∈ κ ↔ ∃ v z w, q = H.op v w ∧ H.App π v z ∧ H.App σ z w

/-- `κ` is the inverse of `π`. -/
def IsInvOf (H : Host) (κ π : H.W) : Prop :=
  ∀ q, q ∈ κ ↔ ∃ v w, q = H.op w v ∧ H.App π v w

theorem isCompOf_comp (σ π : H.W) : H.IsCompOf (H.comp σ π) σ π := by
  intro q
  constructor
  · intro hq
    exact (H.mem_sepS.mp hq).2
  · rintro ⟨v, z, w, e, h1, h2⟩
    rw [e]
    exact H.app_iff.mp (app_comp.mpr ⟨z, h1, h2⟩)

theorem isCompOf_unique {κ σ π : H.W} (h : H.IsCompOf κ σ π) : κ = H.comp σ π :=
  H.ext' fun q => (h q).trans (isCompOf_comp σ π q).symm

theorem isInvOf_inv (π : H.W) : H.IsInvOf (H.inv π) π := by
  intro q
  constructor
  · intro hq
    exact (H.mem_sepS.mp hq).2
  · rintro ⟨v, w, e, h⟩
    rw [e]
    exact H.app_iff.mp (app_inv.mpr h)

theorem isInvOf_unique {κ π : H.W} (h : H.IsInvOf κ π) : κ = H.inv π :=
  H.ext' fun q => (h q).trans (isInvOf_inv π q).symm

/-- The invariants of the level `β`, stated through the record of the level. -/
def Inv (H : Host) (M Mp d Λ F β : H.W) : Prop :=
  ∀ τ G A N D, H.Rec F β τ G A N D →
    (∀ π x, π ∈ G → x ∈ τ → ∃ y, y ∈ τ ∧ H.ActRaw F β π x y) ∧
    (∀ π σ κ x y z, π ∈ G → σ ∈ G → H.IsCompOf κ σ π → x ∈ τ → H.ActRaw F β π x y →
      H.ActRaw F β σ y z → H.ActRaw F β κ x z) ∧
    (∀ π κ x y, π ∈ G → H.IsInvOf κ π → x ∈ τ → H.ActRaw F β π x y → H.ActRaw F β κ y x) ∧
    (∀ c, c ∈ N → ∃ La, H.App Λ (H.suc β) La ∧ c ∈ La) ∧
    (∀ c S, H.Desc M d F (H.suc β) β c S → ∃ y, H.op c (H.op S y) ∈ D) ∧
    (∀ c S y y', H.op c (H.op S y) ∈ D → H.op c (H.op S y') ∈ D → y = y') ∧
    (∀ c S y, H.op c (H.op S y) ∈ D → y ∈ τ ∧ H.Desc M d F (H.suc β) β c S) ∧
    (∀ x, x ∈ τ → ∃ c S, H.op c (H.op S x) ∈ D) ∧
    (∀ π c S S' y y', π ∈ G → H.op c (H.op S y) ∈ D → H.Desc M d F (H.suc β) β c S' →
      (∀ j v, H.App S j v → ∃ w, H.App S' j w ∧ H.App π v w) → H.ActRaw F β π y y' →
      H.op c (H.op S' y') ∈ D) ∧
    (∀ c S y, H.op c (H.op S y) ∈ D → H.SuppTup F G β S y) ∧
    (β ∈ d → τ ∈ Mp) ∧
    (∀ b l, H.IsLabel M b → H.IsLit M b l → l ∈ τ)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem def_inv (M Mp d Λ F : H.W) : Def1 H (H.Inv M Mp d Λ F) := by hdef

namespace Tower

variable (T : Tower H)

theorem inv_of_invT {β : H.W} (hβ : T.Proper β) (h : T.InvT β) :
    H.Inv T.M T.Mp T.d T.Λ T.F β := by
  intro τ G A N D hr
  obtain ⟨e1, e2, e3, e4, e5⟩ := T.rec_unique hβ hr
  rw [e1, e2, e4, e5]
  exact ⟨h.act_tot, fun π σ κ x y z hπ hσ hκ hx h1 h2 => by
      rw [isCompOf_unique hκ]
      exact h.act_comp π σ x y z hπ hσ hx h1 h2,
    fun π κ x y hπ hκ hx h1 => by
      rw [isInvOf_unique hκ]
      exact h.act_inv π x y hπ hx h1,
    h.names, h.dec_tot, h.dec_fun, h.dec_mem, h.dec_surj, h.dec_equi, h.dec_supp, h.tp_mem, h.lit⟩

theorem invT_of_inv {β : H.W} (hβ : T.Proper β) (h : H.Inv T.M T.Mp T.d T.Λ T.F β) :
    T.InvT β := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h _ _ _ _ _ (T.spec hβ).1
  exact ⟨h1, fun π σ x y z hπ hσ hx a b => h2 π σ _ x y z hπ hσ (isCompOf_comp σ π) hx a b,
    fun π x y hπ hx a => h3 π _ x y hπ (isInvOf_inv π) hx a, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- **Every proper level satisfies the invariants.** -/
theorem invT_all : ∀ β, T.Proper β → T.InvT β := by
  intro β hβ
  by_contra hcon
  have hP : Def1 H (fun β => β ∈ H.suc T.d ∧ β ≠ H.emp ∧ ¬ H.Inv T.M T.Mp T.d T.Λ T.F β) := by
    have h := def_inv T.M T.Mp T.d T.Λ T.F
    hdef
  obtain ⟨m, ⟨hm1, hm2, hm3⟩, hmin⟩ := H.least' _ hP (a := β)
    ⟨hβ.1, hβ.2, fun h => hcon (T.invT_of_inv hβ h)⟩
  have hmP : T.Proper m := ⟨hm1, hm2⟩
  refine hm3 (T.inv_of_invT hmP (T.invT_step hmP (fun γ hγm hγ => T.invT_of_inv hγ ?_)))
  by_contra hγI
  exact hmin γ (H.mem_lt _ _ hγm) ⟨hγ.1, hγ.2, hγI⟩

end Tower

end Host


/-! ## Membership between levels: extensionality and equivariance -/

namespace Host

variable {H : Host}

/-- `z`, of the level `b`, is a member of the object `x` of the stage `a`. -/
def Mem (H : Host) (M d F a b z x : H.W) : Prop :=
  ∃ β D, x = H.op β D ∧ ((β = b ∧ z ∈ D) ∨ (β ≠ b ∧ ∃ c S X' η y, H.Desc M d F a β c S ∧
    H.InD M d F a β c S y ∧ y ∈ D ∧ H.label (H.op β b) (H.op c S) X' η ∈ M ∧
    H.IsLit M (H.label (H.op β b) (H.op c S) X' η) z))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem def_mem (M d F a b : H.W) : Def2 H (H.Mem M d F a b) := by hdef

namespace Tower

variable (T : Tower H)

/-- The invariants hold below every stage. -/
theorem hI (α : H.W) : ∀ γ, γ ∈ α → T.Proper γ → T.InvT γ := fun γ _ hγ => T.invT_all γ hγ

theorem mem_of_ext {a b x E z : H.W} (h : T.Ext a x b E) :
    H.Mem T.M T.d T.F a b z x ↔ z ∈ E := by
  obtain ⟨β, D, e, h⟩ := h
  constructor
  · rintro ⟨β', D', e', h'⟩
    obtain ⟨e1, e2⟩ := H.op_inj (e.symm.trans e')
    rw [← e1, ← e2] at h'
    rcases h with ⟨hb, hE⟩ | ⟨hb, halt⟩
    · rcases h' with ⟨-, hz⟩ | ⟨hb', -⟩
      · rw [hE]
        exact hz
      · exact (hb' hb).elim
    · rcases h' with ⟨hb', -⟩ | ⟨-, hw⟩
      · exact (hb hb').elim
      · exact (halt z).mpr hw
  · intro hz
    refine ⟨β, D, e, ?_⟩
    rcases h with ⟨hb, hE⟩ | ⟨hb, halt⟩
    · rw [hE] at hz
      exact Or.inl ⟨hb, hz⟩
    · exact Or.inr ⟨hb, (halt z).mp hz⟩

/-- The extension of an object at a proper lower level exists. -/
theorem ext_ex {a b x : H.W} (ha : T.Proper a) (hx : x ∈ T.Tp a) (hba : b ∈ a)
    (hb0 : b ≠ H.emp) : ∃ E, T.Ext a x b E ∧ ∀ z, z ∈ E → z ∈ T.Tp b := by
  obtain ⟨β, D, e, hβa, hD⟩ := T.obj_pre ha hx
  by_cases hβ : β = b
  · refine ⟨D, ⟨β, D, e, Or.inl ⟨hβ, rfl⟩⟩, fun z hz => ?_⟩
    have h := hD z hz
    rw [hβ, T.Ts_of_ne hb0] at h
    exact h
  · obtain ⟨E, hE, hET⟩ := T.alt_ex ha (β := β) (D := D) hba hb0
    exact ⟨E, ⟨β, D, e, Or.inr ⟨hβ, hE⟩⟩, hET⟩

theorem mem_Tp {a b x z : H.W} (ha : T.Proper a) (hx : x ∈ T.Tp a) (hba : b ∈ a)
    (hb0 : b ≠ H.emp) (h : H.Mem T.M T.d T.F a b z x) : z ∈ T.Tp b := by
  obtain ⟨E, hE, hET⟩ := T.ext_ex ha hx hba hb0
  exact hET z ((T.mem_of_ext hE).mp h)

/-- Only the empty object has an empty extension. -/
theorem ext_emp {a b x : H.W} (ha : T.Proper a) (hx : x ∈ T.Tp a) (hba : b ∈ a)
    (h : T.Ext a x b H.emp) : x = H.op H.emp H.emp := by
  rcases T.obj_cases ha hx with h0 | ⟨β, D, e, hD0, hβa, hD, -⟩
  · exact h0
  · exfalso
    obtain ⟨β', D', e', h'⟩ := h
    obtain ⟨e1, e2⟩ := H.op_inj (e.symm.trans e')
    rw [← e1, ← e2] at h'
    rcases h' with ⟨-, hE⟩ | ⟨hb, halt⟩
    · exact hD0 hE.symm
    · obtain ⟨z, hz⟩ := H.ne_emp hD0
      obtain ⟨c, S, hdesc, hdec⟩ := T.ex_desc ha (T.hI a) hβa (hD z hz)
      obtain ⟨hcM, hSM⟩ := T.desc_mem_M ha (T.hI a) hβa hdesc
      have hbM : H.label (H.op β b) (H.op c S) H.emp H.emp ∈ T.M :=
        T.hM.label_mem (T.hM.op_mem (T.lvl_mem ha hβa) (T.lvl_mem ha hba))
          (T.hM.op_mem hcM hSM) T.hM.emp_mem T.hM.emp_mem
      obtain ⟨l, hl⟩ := H.lit_ex T.M (H.label (H.op β b) (H.op c S) H.emp H.emp)
      exact H.not_mem_emp l ((halt l).mpr ⟨c, S, _, _, z, hdesc, hdec, hz, hbM, hl⟩)

/-- **Extensionality** for the membership relation, at every proper lower level. -/
theorem ext_full {a b x y : H.W} (ha : T.Proper a) (hx : x ∈ T.Tp a) (hy : y ∈ T.Tp a)
    (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (h : ∀ z, z ∈ T.Tp b → (H.Mem T.M T.d T.F a b z x ↔ H.Mem T.M T.d T.F a b z y)) : x = y := by
  obtain ⟨E, hE, hET⟩ := T.ext_ex ha hx hba hb0
  obtain ⟨E', hE', hET'⟩ := T.ext_ex ha hy hba hb0
  have e : E' = E := H.ext' fun z =>
    ⟨fun hz => (T.mem_of_ext hE).mp ((h z (hET' z hz)).mpr ((T.mem_of_ext hE').mpr hz)),
      fun hz => (T.mem_of_ext hE').mp ((h z (hET z hz)).mp ((T.mem_of_ext hE).mpr hz))⟩
  rw [e] at hE'
  by_cases h0 : E = H.emp
  · rw [h0] at hE hE'
    rw [T.ext_emp ha hx hba hE, T.ext_emp ha hy hba hE']
  · exact T.ext_stage ha (T.hI a) hx hy hba hb0 hE hE' h0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **Membership is equivariant** under the automorphisms of the stage. -/
theorem mem_equi {a b π x x' z z' : H.W} (ha : T.Proper a) (hπ : H.IsAut T.M T.d T.F a π)
    (hx : x ∈ T.Tp a) (hact : H.ActRaw T.F a π x x') (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hz : z ∈ T.Tp b) (hzz : H.ActLow T.F a π b z z') :
    H.Mem T.M T.d T.F a b z x ↔ H.Mem T.M T.d T.F a b z' x' := by
  have hI := T.hI a
  obtain ⟨β, D, e, hβa, hD⟩ := T.obj_pre ha hx
  obtain ⟨β1, D1, D', e1, e2, hD'⟩ := id hact
  obtain ⟨e3, e4⟩ := H.op_inj (e.symm.trans e1)
  rw [← e3] at e2 hD'
  rw [← e4] at hD'
  have hzT : z ∈ T.Ts b := by
    rw [T.Ts_of_ne hb0]
    exact hz
  have inj : ∀ z0, z0 ∈ T.Ts b → H.ActLow T.F a π b z0 z' → z0 = z := fun z0 hz0 h0 =>
    T.low_fun (isAut_inv hπ).1.1 (T.low_inv ha hI hπ hba hz0 h0) (T.low_inv ha hI hπ hba hzT hzz)
  by_cases hβ : β = b
  · have hEx : T.Ext a x b D := ⟨β, D, e, Or.inl ⟨hβ, rfl⟩⟩
    have hEx' : T.Ext a x' b D' := ⟨β, D', e2, Or.inl ⟨hβ, rfl⟩⟩
    have hD'b : ∀ z', z' ∈ D' ↔ ∃ z, z ∈ D ∧ H.ActLow T.F a π b z z' := by
      rw [← hβ]
      exact hD'
    have hDb : ∀ z, z ∈ D → z ∈ T.Ts b := by
      rw [← hβ]
      exact hD
    rw [T.mem_of_ext hEx, T.mem_of_ext hEx', hD'b z']
    exact ⟨fun h => ⟨z, h, hzz⟩, fun ⟨z0, hz0, h0⟩ => by
      rw [← inj z0 (hDb z0 hz0) h0]
      exact hz0⟩
  · obtain ⟨E, hE, hET⟩ := T.alt_ex ha (β := β) (D := D) hba hb0
    obtain ⟨Y₂, hY₂⟩ := H.sep' (T.Tp b) (fun l' => ∃ l, l ∈ E ∧ H.ActLow T.F a π b l l') (by hdef)
    have hETs : ∀ l, l ∈ E → l ∈ T.Ts b := fun l hl => by
      rw [T.Ts_of_ne hb0]
      exact hET l hl
    have hY₂' : ∀ l', l' ∈ Y₂ ↔ ∃ l, l ∈ E ∧ H.ActLow T.F a π b l l' := fun l' =>
      ⟨fun h => ((hY₂ l').mp h).2, fun h => (hY₂ l').mpr ⟨by
        obtain ⟨l, hl, hll⟩ := h
        have h1 := T.low_mem ha hI hπ hba (hETs l hl) hll
        rw [T.Ts_of_ne hb0] at h1
        exact h1, h⟩⟩
    have halt' := T.alt_transport ha hI hπ hβa hba hb0 hβ hD hE hD' hY₂'
    have hEx : T.Ext a x b E := ⟨β, D, e, Or.inr ⟨hβ, hE⟩⟩
    have hEx' : T.Ext a x' b Y₂ := ⟨β, D', e2, Or.inr ⟨hβ, halt'⟩⟩
    rw [T.mem_of_ext hEx, T.mem_of_ext hEx', hY₂' z']
    exact ⟨fun h => ⟨z, h, hzz⟩, fun ⟨z0, hz0, h0⟩ => by
      rw [← inj z0 (hETs z0 hz0) h0]
      exact hz0⟩

end Tower

end Host


/-! ## Chains of levels: the action of the top group on every level, and raised supports -/

namespace Host

variable {H : Host}

theorem bun_emp (a : H.W) : H.bun a H.emp = a :=
  H.ext' fun z => by
    rw [H.mem_bun]
    exact ⟨fun h => h.elim id (fun h => (H.not_mem_emp z h).elim), Or.inl⟩

/-- The derivative, as a term. -/
noncomputable def derS (H : Host) (M π α β : H.W) : H.W :=
  H.sepS M (fun q => ∃ t u t', q = H.op (H.op t u) (H.op t' u) ∧ H.PType u β ∧
    H.App π (H.op t (H.bun u (H.sg α))) (H.op t' (H.bun u (H.sg α)))) (by hdef)

theorem isDer_derS {M π α β : H.W} (hM : H.Closed M) (hπ : H.Sub π M) :
    H.IsDer π α β (H.derS M π α β) := by
  intro q
  constructor
  · intro hq
    exact (H.mem_sepS.mp hq).2
  · intro h
    refine H.mem_sepS.mpr ⟨?_, h⟩
    obtain ⟨t, u, t', e, -, happ⟩ := h
    have h1 := hM.of_op_mem (hπ _ (H.app_iff.mp happ))
    have h2 := hM.of_op_mem h1.1
    have h3 := hM.of_op_mem h1.2
    have hu : u ∈ M := hM.sub u _ (fun x hx => H.mem_bun.mpr (Or.inl hx)) h2.2
    rw [e]
    exact hM.op_mem (hM.op_mem h2.1 hu) (hM.op_mem h3.1 hu)

/-- The levels of the chain above the index `i`, as a set. -/
noncomputable def chainSet (H : Host) (t : ℕ → H.W) : ℕ → H.W
  | 0 => H.emp
  | i + 1 => H.bun (H.sg (t i)) (H.chainSet t i)

namespace Tower

variable (T : Tower H)

/-- A descending chain of proper levels `t 0 ∋ t 1 ∋ … ∋ t k`. -/
structure Chain (t : ℕ → H.W) (k : ℕ) : Prop where
  top : T.Proper (t 0)
  desc : ∀ i, i < k → t (i + 1) ∈ t i ∧ t (i + 1) ≠ H.emp

theorem chain_proper {t : ℕ → H.W} {k : ℕ} (hc : T.Chain t k) : ∀ i, i ≤ k → T.Proper (t i) := by
  intro i
  induction i with
  | zero => exact fun _ => hc.top
  | succ i ih =>
    exact fun hi => T.lower_proper (ih (by omega)) (hc.desc i (by omega)).1 (hc.desc i (by omega)).2

/-- The action of an automorphism of the top stage on the levels of the chain: the iterated
derivative along the chain. -/
noncomputable def derN (t : ℕ → H.W) (π : H.W) : ℕ → H.W
  | 0 => π
  | i + 1 => H.derS T.M (derN t π i) (t i) (t (i + 1))

theorem derN_aut {t : ℕ → H.W} {k : ℕ} {π : H.W} (hc : T.Chain t k)
    (hπ : H.IsAut T.M T.d T.F (t 0) π) :
    ∀ i, i ≤ k → H.IsAut T.M T.d T.F (t i) (T.derN t π i) := by
  intro i
  induction i with
  | zero => exact fun _ => hπ
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    have hp := T.chain_proper hc i (by omega)
    exact der_aut (T.proper_om hp) hp.1 (hc.desc i (by omega)).1 (hc.desc i (by omega)).2 h
      (isDer_derS T.hM (aut_sub T.hM T.hdM h.1))

theorem derN_der {t : ℕ → H.W} {k : ℕ} {π : H.W} (hc : T.Chain t k)
    (hπ : H.IsAut T.M T.d T.F (t 0) π) {i : ℕ} (hi : i < k) :
    H.IsDer (T.derN t π i) (t i) (t (i + 1)) (T.derN t π (i + 1)) :=
  isDer_derS T.hM (aut_sub T.hM T.hdM (T.derN_aut hc hπ i (by omega)).1)

/-- The action on the level `t (i+1)`, seen from the stage `t i`. -/
theorem actN_low {t : ℕ → H.W} {k : ℕ} {π z z' : H.W} (hc : T.Chain t k)
    (hπ : H.IsAut T.M T.d T.F (t 0) π) {i : ℕ} (hi : i < k) :
    H.ActLow T.F (t i) (T.derN t π i) (t (i + 1)) z z' ↔
      z ∈ T.Tp (t (i + 1)) ∧ H.ActRaw T.F (t (i + 1)) (T.derN t π (i + 1)) z z' :=
  T.low_proper (T.chain_proper hc i (by omega)) (T.invT_all _ (T.chain_proper hc (i + 1) (by omega)))
    (hc.desc i hi).1 (hc.desc i hi).2 (T.derN_aut hc hπ i (by omega)) (T.derN_der hc hπ hi)

/-- A token of the level `t i`, raised along the chain, is a token of the top stage. -/
theorem tok_raiseN {t : ℕ → H.W} {k : ℕ} (hc : T.Chain t k) :
    ∀ i, i ≤ k → ∀ v u, H.IsTok T.M T.d (t i) (H.op v u) →
      H.IsTok T.M T.d (t 0) (H.op v (H.bun u (H.chainSet t i))) := by
  intro i
  induction i with
  | zero =>
    intro _ v u h
    show H.IsTok T.M T.d (t 0) (H.op v (H.bun u H.emp))
    rw [bun_emp]
    exact h
  | succ i ih =>
    intro hi v u h
    have hp := T.chain_proper hc i (by omega)
    have h1 := tok_raise (T.proper_om hp) (hc.desc i (by omega)).1 hp.1 h
    have h2 := ih (by omega) v _ h1
    rw [bun_assoc] at h2
    exact h2

/-- If the automorphism fixes the raised token, its action on the level fixes the token. -/
theorem derN_app {t : ℕ → H.W} {k : ℕ} {π : H.W} (hc : T.Chain t k)
    (hπ : H.IsAut T.M T.d T.F (t 0) π) :
    ∀ i, i ≤ k → ∀ v v' u, H.PType u (t i) →
      H.App π (H.op v (H.bun u (H.chainSet t i))) (H.op v' (H.bun u (H.chainSet t i))) →
      H.App (T.derN t π i) (H.op v u) (H.op v' u) := by
  intro i
  induction i with
  | zero =>
    intro _ v v' u _ h
    have h' : H.App π (H.op v (H.bun u H.emp)) (H.op v' (H.bun u H.emp)) := h
    rw [bun_emp] at h'
    exact h'
  | succ i ih =>
    intro hi v v' u hu h
    have hp := T.chain_proper hc i (by omega)
    have h' : H.App π (H.op v (H.bun u (H.bun (H.sg (t i)) (H.chainSet t i))))
        (H.op v' (H.bun u (H.bun (H.sg (t i)) (H.chainSet t i)))) := h
    rw [← bun_assoc] at h'
    have hu' : H.PType (H.bun u (H.sg (t i))) (t i) :=
      Or.inr ⟨H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl)), fun x hx => by
        rcases H.mem_bun.mp hx with hx | hx
        · exact H.mem_suc.mpr (Or.inl (ptype_lt (T.proper_om hp) (hc.desc i (by omega)).1 hu hx))
        · exact H.mem_suc.mpr (Or.inr (H.mem_sg.mp hx))⟩
    exact (der_app (T.derN_der hc hπ (by omega))).mpr ⟨v, u, v', rfl, rfl, hu,
      ih (by omega) v v' _ hu' h'⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **Raised supports.** An object of a level of the chain has a finite set of tokens of the top
stage such that every automorphism of the top stage that fixes these tokens fixes the object,
through its action on that level. -/
theorem supp_raise {t : ℕ → H.W} {k : ℕ} (hc : T.Chain t k) {i : ℕ} (hi : i ≤ k) {x : H.W}
    (hx : x ∈ T.Tp (t i)) :
    ∃ Sp, H.Fin Sp ∧ (∀ v, v ∈ Sp → H.IsTok T.M T.d (t 0) v) ∧
      (∀ π, H.IsAut T.M T.d T.F (t 0) π → (∀ v, v ∈ Sp → H.App π v v) →
        H.ActRaw T.F (t i) (T.derN t π i) x x) ∧
      ∀ v, v ∈ Sp → ∃ v0 u, v = H.op v0 (H.bun u (H.chainSet t i)) ∧ H.PType u (t i) := by
  have hp := T.chain_proper hc i hi
  obtain ⟨-, β0, D0, -, -, Sx, hfin, htok, hsupp⟩ := ((T.spec hp).2.2.1 x).mp hx
  have hR : Def2 H (fun w w' => ∃ v u, w = H.op v u ∧ w' = H.op v (H.bun u (H.chainSet t i))) := by
    hdef
  have hRf : ∀ w ∈ Sx, ∀ w' w'', (∃ v u, w = H.op v u ∧ w' = H.op v (H.bun u (H.chainSet t i))) →
      (∃ v u, w = H.op v u ∧ w'' = H.op v (H.bun u (H.chainSet t i))) → w' = w'' := by
    rintro w - w' w'' ⟨v, u, e, ew⟩ ⟨v2, u2, e2, ew2⟩
    obtain ⟨e3, e4⟩ := H.op_inj (e.symm.trans e2)
    rw [ew, ew2, e3, e4]
  obtain ⟨r, hrf, hr⟩ : ∃ r, H.IsFun r ∧ ∀ w w', H.App r w w' ↔
      w ∈ Sx ∧ ∃ v u, w = H.op v u ∧ w' = H.op v (H.bun u (H.chainSet t i)) :=
    ⟨H.mkFun Sx _ hR hRf, H.isFun_mkFun, fun w w' => H.app_mkFun⟩
  obtain ⟨Sp, hSpfin, hSp⟩ := fin_image hfin hrf (fun w hw => by
    obtain ⟨v, u, e, -⟩ := htok w hw
    exact ⟨_, (hr _ _).mpr ⟨hw, v, u, e, rfl⟩⟩)
  refine ⟨Sp, hSpfin, fun w' hw' => ?_, fun π hπ hfix => ?_, fun w' hw' => ?_⟩
  · obtain ⟨w, hw, hww'⟩ := (hSp w').mp hw'
    obtain ⟨-, v, u, e, ew⟩ := (hr _ _).mp hww'
    rw [ew]
    have h := htok w hw
    rw [e] at h
    exact T.tok_raiseN hc i hi v u h
  · refine hsupp _ ((T.mem_Gs hp).mpr (T.derN_aut hc hπ i hi)) (fun w hw => ?_)
    obtain ⟨v, u, e, hpath, hty, -⟩ := id (htok w hw)
    rw [e]
    exact T.derN_app hc hπ i hi v v u hty
      (hfix _ ((hSp _).mpr ⟨w, hw, (hr _ _).mpr ⟨hw, v, u, e, rfl⟩⟩))
  · obtain ⟨w, hw, hww'⟩ := (hSp w').mp hw'
    obtain ⟨-, v, u, e, ew⟩ := (hr _ _).mp hww'
    obtain ⟨v1, u1, e1, -, hty, -⟩ := id (htok w hw)
    obtain ⟨-, e3⟩ := H.op_inj (e.symm.trans e1)
    rw [← e3] at hty
    exact ⟨v, u, ew, hty⟩

end Tower

end Host


/-! ## Formulas over a chain of levels: invariance, definability, predicative comprehension -/

namespace Host

variable {H : Host}

/-- Formulas over a chain of levels. A variable is a pair (index in the chain, name); the
variable `(i, x)` ranges over the objects of the level `t i`. `mem i x y` says that the variable
`(i+1, x)` is a member of the variable `(i, y)`. -/
inductive CForm : Type
  | mem (i x y : ℕ)
  | eq (i x y : ℕ)
  | neg (φ : CForm)
  | and (φ ψ : CForm)
  | or (φ ψ : CForm)
  | imp (φ ψ : CForm)
  | iff (φ ψ : CForm)
  | all (i x : ℕ) (φ : CForm)
  | ex (i x : ℕ) (φ : CForm)

/-- All the indices of the formula are indices of the chain `t 0, …, t k`. -/
def CForm.Ok (k : ℕ) : CForm → Prop
  | .mem i _ _ => i + 1 ≤ k
  | .eq i _ _ => i ≤ k
  | .neg φ => φ.Ok k
  | .and φ ψ => φ.Ok k ∧ ψ.Ok k
  | .or φ ψ => φ.Ok k ∧ ψ.Ok k
  | .imp φ ψ => φ.Ok k ∧ ψ.Ok k
  | .iff φ ψ => φ.Ok k ∧ ψ.Ok k
  | .all i _ φ => i ≤ k ∧ φ.Ok k
  | .ex i _ φ => i ≤ k ∧ φ.Ok k

/-- The translation into formulas of the host, with one relation symbol for each index. -/
def CForm.tr : CForm → Form
  | .mem i x y => .rel i (Nat.pair (i + 1 + 1) x) (Nat.pair (i + 1) y) (Nat.pair 0 0)
  | .eq i x y => .eq (Nat.pair (i + 1) x) (Nat.pair (i + 1) y)
  | .neg φ => .neg φ.tr
  | .and φ ψ => .and φ.tr ψ.tr
  | .or φ ψ => .or φ.tr ψ.tr
  | .imp φ ψ => .imp φ.tr ψ.tr
  | .iff φ ψ => .iff φ.tr ψ.tr
  | .all i x φ => .all (Nat.pair (i + 1) x) (.imp (.mem (Nat.pair (i + 1) x) (Nat.pair 0 i)) φ.tr)
  | .ex i x φ => .ex (Nat.pair (i + 1) x) (.and (.mem (Nat.pair (i + 1) x) (Nat.pair 0 i)) φ.tr)

/-- Update of a two-dimensional environment. -/
def upd2 {W : Type} (ρ : ℕ → ℕ → W) (i x : ℕ) (v : W) : ℕ → ℕ → W :=
  fun j y => if j = i ∧ y = x then v else ρ j y

theorem upd2_same {W : Type} (ρ : ℕ → ℕ → W) (i x : ℕ) (v : W) : upd2 ρ i x v i x = v := by
  simp [upd2]

theorem upd2_ne {W : Type} (ρ : ℕ → ℕ → W) {i x j y : ℕ} (v : W) (h : ¬ (j = i ∧ y = x)) :
    upd2 ρ i x v j y = ρ j y := by
  simp [upd2, h]

namespace Tower

variable (T : Tower H)

/-- Satisfaction of a formula over the chain `t`. -/
def Sat (t : ℕ → H.W) : CForm → (ℕ → ℕ → H.W) → Prop
  | .mem i x y, ρ => H.Mem T.M T.d T.F (t i) (t (i + 1)) (ρ (i + 1) x) (ρ i y)
  | .eq i x y, ρ => ρ i x = ρ i y
  | .neg φ, ρ => ¬ Sat t φ ρ
  | .and φ ψ, ρ => Sat t φ ρ ∧ Sat t ψ ρ
  | .or φ ψ, ρ => Sat t φ ρ ∨ Sat t ψ ρ
  | .imp φ ψ, ρ => Sat t φ ρ → Sat t ψ ρ
  | .iff φ ψ, ρ => (Sat t φ ρ ↔ Sat t ψ ρ)
  | .all i x φ, ρ => ∀ v, v ∈ T.Tp (t i) → Sat t φ (upd2 ρ i x v)
  | .ex i x φ, ρ => ∃ v, v ∈ T.Tp (t i) ∧ Sat t φ (upd2 ρ i x v)

/-- `ρ'` is the image of the environment `ρ` under the action of `π` along the chain. -/
def Moves (t : ℕ → H.W) (k : ℕ) (π : H.W) (ρ ρ' : ℕ → ℕ → H.W) : Prop :=
  ∀ i, i ≤ k → ∀ x, ρ i x ∈ T.Tp (t i) ∧ H.ActRaw T.F (t i) (T.derN t π i) (ρ i x) (ρ' i x)

theorem moves_upd {t : ℕ → H.W} {k : ℕ} {π : H.W} {ρ ρ' : ℕ → ℕ → H.W} {i x : ℕ} {v v' : H.W}
    (h : T.Moves t k π ρ ρ') (hv : v ∈ T.Tp (t i))
    (hact : H.ActRaw T.F (t i) (T.derN t π i) v v') :
    T.Moves t k π (upd2 ρ i x v) (upd2 ρ' i x v') := by
  intro j hj y
  by_cases hc : j = i ∧ y = x
  · rw [hc.1, hc.2, upd2_same, upd2_same]
    exact ⟨hv, hact⟩
  · rw [upd2_ne _ _ hc, upd2_ne _ _ hc]
    exact h j hj y

theorem act_fwd {a σ v : H.W} (ha : T.Proper a) (hσ : H.IsAut T.M T.d T.F a σ)
    (hv : v ∈ T.Tp a) : ∃ v', v' ∈ T.Tp a ∧ H.ActRaw T.F a σ v v' :=
  (T.invT_all a ha).act_tot σ v ((T.mem_Gs ha).mpr hσ) hv

theorem act_bwd {a σ v' : H.W} (ha : T.Proper a) (hσ : H.IsAut T.M T.d T.F a σ)
    (hv' : v' ∈ T.Tp a) : ∃ v, v ∈ T.Tp a ∧ H.ActRaw T.F a σ v v' := by
  have hinv := (T.mem_Gs ha).mpr (isAut_inv hσ)
  obtain ⟨v, hv, hact⟩ := (T.invT_all a ha).act_tot _ v' hinv hv'
  have h := (T.invT_all a ha).act_inv _ v' v hinv hv' hact
  rw [inv_inv hσ.1.1.1] at h
  exact ⟨v, hv, h⟩

theorem act_inj {a σ v w v' : H.W} (ha : T.Proper a) (hσ : H.IsAut T.M T.d T.F a σ)
    (hv : v ∈ T.Tp a) (hw : w ∈ T.Tp a) (h1 : H.ActRaw T.F a σ v v')
    (h2 : H.ActRaw T.F a σ w v') : v = w := by
  have hG := (T.mem_Gs ha).mpr hσ
  exact actRaw_fun ((T.invT_all a ha).act_inv σ v v' hG hv h1)
    ((T.invT_all a ha).act_inv σ w v' hG hw h2)

theorem act_mem {a σ v v' : H.W} (ha : T.Proper a) (hσ : H.IsAut T.M T.d T.F a σ)
    (hv : v ∈ T.Tp a) (h : H.ActRaw T.F a σ v v') : v' ∈ T.Tp a := by
  obtain ⟨w, hw, hact⟩ := T.act_fwd ha hσ hv
  rw [actRaw_fun h hact]
  exact hw

/-- **Invariance.** Satisfaction is invariant under the action of the top group along the
chain. -/
theorem sat_equi {t : ℕ → H.W} {k : ℕ} {π : H.W} (hc : T.Chain t k)
    (hπ : H.IsAut T.M T.d T.F (t 0) π) :
    ∀ φ : CForm, φ.Ok k → ∀ ρ ρ', T.Moves t k π ρ ρ' → (T.Sat t φ ρ ↔ T.Sat t φ ρ') := by
  intro φ
  induction φ with
  | mem i x y =>
    intro hi ρ ρ' hm
    have hi' : i + 1 ≤ k := hi
    obtain ⟨hy, hyact⟩ := hm i (by omega) y
    obtain ⟨hx, hxact⟩ := hm (i + 1) hi' x
    exact T.mem_equi (T.chain_proper hc i (by omega)) (T.derN_aut hc hπ i (by omega)) hy hyact
      (hc.desc i (by omega)).1 (hc.desc i (by omega)).2 hx
      ((T.actN_low hc hπ (by omega)).mpr ⟨hx, hxact⟩)
  | eq i x y =>
    intro hi ρ ρ' hm
    have hi' : i ≤ k := hi
    obtain ⟨hx, hxact⟩ := hm i hi' x
    obtain ⟨hy, hyact⟩ := hm i hi' y
    show ρ i x = ρ i y ↔ ρ' i x = ρ' i y
    constructor
    · intro e
      rw [e] at hxact
      exact actRaw_fun hxact hyact
    · intro e
      rw [e] at hxact
      exact T.act_inj (T.chain_proper hc i hi') (T.derN_aut hc hπ i hi') hx hy hxact hyact
  | neg φ ih =>
    intro hok ρ ρ' hm
    exact not_congr (ih hok ρ ρ' hm)
  | and φ ψ ih1 ih2 =>
    intro hok ρ ρ' hm
    exact and_congr (ih1 hok.1 ρ ρ' hm) (ih2 hok.2 ρ ρ' hm)
  | or φ ψ ih1 ih2 =>
    intro hok ρ ρ' hm
    exact or_congr (ih1 hok.1 ρ ρ' hm) (ih2 hok.2 ρ ρ' hm)
  | imp φ ψ ih1 ih2 =>
    intro hok ρ ρ' hm
    exact imp_congr (ih1 hok.1 ρ ρ' hm) (ih2 hok.2 ρ ρ' hm)
  | iff φ ψ ih1 ih2 =>
    intro hok ρ ρ' hm
    exact iff_congr (ih1 hok.1 ρ ρ' hm) (ih2 hok.2 ρ ρ' hm)
  | all i x φ ih =>
    intro hok ρ ρ' hm
    have hp := T.chain_proper hc i hok.1
    have hσ := T.derN_aut hc hπ i hok.1
    constructor
    · intro h v' hv'
      obtain ⟨v, hv, hact⟩ := T.act_bwd hp hσ hv'
      exact (ih hok.2 _ _ (T.moves_upd hm hv hact)).mp (h v hv)
    · intro h v hv
      obtain ⟨v', hv', hact⟩ := T.act_fwd hp hσ hv
      exact (ih hok.2 _ _ (T.moves_upd hm hv hact)).mpr (h v' hv')
  | ex i x φ ih =>
    intro hok ρ ρ' hm
    have hp := T.chain_proper hc i hok.1
    have hσ := T.derN_aut hc hπ i hok.1
    constructor
    · rintro ⟨v, hv, h⟩
      obtain ⟨v', hv', hact⟩ := T.act_fwd hp hσ hv
      exact ⟨v', hv', (ih hok.2 _ _ (T.moves_upd hm hv hact)).mp h⟩
    · rintro ⟨v', hv', h⟩
      obtain ⟨v, hv, hact⟩ := T.act_bwd hp hσ hv'
      exact ⟨v, hv, (ih hok.2 _ _ (T.moves_upd hm hv hact)).mpr h⟩

/-- The environment of the host that corresponds to a two-dimensional environment; the
variables `(0, i)` hold the sets of objects of the levels. -/
noncomputable def envOf (t : ℕ → H.W) (ρ : ℕ → ℕ → H.W) : ℕ → H.W :=
  fun n => if (Nat.unpair n).1 = 0 then T.Tp (t (Nat.unpair n).2)
    else ρ ((Nat.unpair n).1 - 1) (Nat.unpair n).2

theorem envOf_var (t : ℕ → H.W) (ρ : ℕ → ℕ → H.W) (i x : ℕ) :
    T.envOf t ρ (Nat.pair (i + 1) x) = ρ i x := by
  simp [envOf, Nat.unpair_pair]

theorem envOf_par (t : ℕ → H.W) (ρ : ℕ → ℕ → H.W) (i : ℕ) :
    T.envOf t ρ (Nat.pair 0 i) = T.Tp (t i) := by
  simp [envOf, Nat.unpair_pair]

theorem envOf_upd (t : ℕ → H.W) (ρ : ℕ → ℕ → H.W) (i x : ℕ) (v : H.W) :
    upd (T.envOf t ρ) (Nat.pair (i + 1) x) v = T.envOf t (upd2 ρ i x v) := by
  funext n
  by_cases h : n = Nat.pair (i + 1) x
  · rw [h, upd_same, envOf_var, upd2_same]
  · rw [upd_ne _ _ h]
    unfold envOf
    by_cases h0 : (Nat.unpair n).1 = 0
    · simp [h0]
    · have hne : ¬ ((Nat.unpair n).1 - 1 = i ∧ (Nat.unpair n).2 = x) := by
        rintro ⟨h1, h2⟩
        apply h
        have h3 : (Nat.unpair n).1 = i + 1 := by omega
        calc n = Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 := (Nat.pair_unpair n).symm
          _ = Nat.pair (i + 1) x := by rw [h3, h2]
      simp [h0, upd2_ne _ _ hne]

theorem holds_tr (t : ℕ → H.W) : ∀ (φ : CForm) (ρ : ℕ → ℕ → H.W),
    Holds H.mem H.lt (fun i z x _ => H.Mem T.M T.d T.F (t i) (t (i + 1)) z x) φ.tr
      (T.envOf t ρ) ↔ T.Sat t φ ρ := by
  intro φ
  induction φ with
  | mem i x y =>
    intro ρ
    show H.Mem T.M T.d T.F (t i) (t (i + 1)) (T.envOf t ρ (Nat.pair (i + 1 + 1) x))
      (T.envOf t ρ (Nat.pair (i + 1) y)) ↔ _
    rw [T.envOf_var t ρ (i + 1) x, T.envOf_var t ρ i y]
    exact Iff.rfl
  | eq i x y =>
    intro ρ
    show T.envOf t ρ (Nat.pair (i + 1) x) = T.envOf t ρ (Nat.pair (i + 1) y) ↔ _
    rw [T.envOf_var, T.envOf_var]
    exact Iff.rfl
  | neg φ ih =>
    intro ρ
    exact not_congr (ih ρ)
  | and φ ψ ih1 ih2 =>
    intro ρ
    exact and_congr (ih1 ρ) (ih2 ρ)
  | or φ ψ ih1 ih2 =>
    intro ρ
    exact or_congr (ih1 ρ) (ih2 ρ)
  | imp φ ψ ih1 ih2 =>
    intro ρ
    exact imp_congr (ih1 ρ) (ih2 ρ)
  | iff φ ψ ih1 ih2 =>
    intro ρ
    exact iff_congr (ih1 ρ) (ih2 ρ)
  | all i x φ ih =>
    intro ρ
    have key : ∀ a, (H.mem (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair (i + 1) x))
        (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair 0 i)) ↔ a ∈ T.Tp (t i)) := fun a => by
      rw [upd_same, upd_ne _ _ (pair_ne_of_fst (c := 0) (c' := i + 1) (by omega)), T.envOf_par]
      exact Iff.rfl
    show (∀ a, H.mem (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair (i + 1) x))
        (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair 0 i)) →
        Holds H.mem H.lt _ φ.tr (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a)) ↔
      ∀ v, v ∈ T.Tp (t i) → T.Sat t φ (upd2 ρ i x v)
    constructor
    · intro h v hv
      have h2 := h v ((key v).mpr hv)
      rw [T.envOf_upd] at h2
      exact (ih _).mp h2
    · intro h a hm
      have h2 := (ih _).mpr (h a ((key a).mp hm))
      rw [← T.envOf_upd] at h2
      exact h2
  | ex i x φ ih =>
    intro ρ
    have key : ∀ a, (H.mem (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair (i + 1) x))
        (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair 0 i)) ↔ a ∈ T.Tp (t i)) := fun a => by
      rw [upd_same, upd_ne _ _ (pair_ne_of_fst (c := 0) (c' := i + 1) (by omega)), T.envOf_par]
      exact Iff.rfl
    show (∃ a, H.mem (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair (i + 1) x))
        (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a (Nat.pair 0 i)) ∧
        Holds H.mem H.lt _ φ.tr (upd (T.envOf t ρ) (Nat.pair (i + 1) x) a)) ↔
      ∃ v, v ∈ T.Tp (t i) ∧ T.Sat t φ (upd2 ρ i x v)
    constructor
    · rintro ⟨a, hm, h⟩
      rw [T.envOf_upd] at h
      exact ⟨a, (key a).mp hm, (ih _).mp h⟩
    · rintro ⟨v, hv, h⟩
      have h2 := (ih _).mpr h
      rw [← T.envOf_upd] at h2
      exact ⟨v, (key v).mpr hv, h2⟩

/-- Satisfaction is definable in the host, in any one variable. -/
theorem def_sat (t : ℕ → H.W) (φ : CForm) (ρ : ℕ → ℕ → H.W) (i x : ℕ) :
    Def1 H (fun z => T.Sat t φ (upd2 ρ i x z)) := by
  have hI : ∀ j, Def3 H (fun z y (_ : H.W) => H.Mem T.M T.d T.F (t j) (t (j + 1)) z y) :=
    fun j => (def_mem T.M T.d T.F (t j) (t (j + 1))).pad
  obtain ⟨D⟩ := exists_relData hI
  refine ⟨elimF D φ.tr, merge D (T.envOf t ρ), Nat.pair 0 (Nat.pair (i + 1) x),
    pure_elimF D _, fun a => ?_⟩
  rw [merge_upd, holds_elimF, T.envOf_upd, T.holds_tr]

/-- A finite set of tokens of the top stage that supports finitely many values of an
environment, each through the action on its level. -/
theorem supp_list {t : ℕ → H.W} {k : ℕ} (hc : T.Chain t k) (ρ : ℕ → ℕ → H.W)
    (hρ : ∀ i, i ≤ k → ∀ x, ρ i x ∈ T.Tp (t i)) :
    ∀ L : List (ℕ × ℕ), ∃ Sp, H.Fin Sp ∧ (∀ v, v ∈ Sp → H.IsTok T.M T.d (t 0) v) ∧
      ∀ π, H.IsAut T.M T.d T.F (t 0) π → (∀ v, v ∈ Sp → H.App π v v) →
        ∀ i x, (i, x) ∈ L → i ≤ k → H.ActRaw T.F (t i) (T.derN t π i) (ρ i x) (ρ i x) := by
  intro L
  induction L with
  | nil =>
    exact ⟨H.emp, H.fin_emp, fun v hv => (H.not_mem_emp v hv).elim,
      fun _ _ _ _ _ h _ => (List.not_mem_nil h).elim⟩
  | cons p L ih =>
    obtain ⟨Sp, hfin, htok, hsupp⟩ := ih
    by_cases hp : p.1 ≤ k
    · obtain ⟨Sp1, hfin1, htok1, hsupp1, -⟩ := T.supp_raise hc hp (hρ p.1 hp p.2)
      refine ⟨H.bun Sp Sp1, H.fin_bun hfin hfin1,
        fun v hv => (H.mem_bun.mp hv).elim (htok v) (htok1 v), fun π hπ hfix i x h hi => ?_⟩
      rcases List.mem_cons.mp h with e | h
      · have e1 : i = p.1 := congrArg Prod.fst e
        have e2 : x = p.2 := congrArg Prod.snd e
        rw [e1, e2]
        exact hsupp1 π hπ (fun v hv => hfix v (H.mem_bun.mpr (Or.inr hv)))
      · exact hsupp π hπ (fun v hv => hfix v (H.mem_bun.mpr (Or.inl hv))) i x h hi
    · refine ⟨Sp, hfin, htok, fun π hπ hfix i x h hi => ?_⟩
      rcases List.mem_cons.mp h with e | h
      · have e1 : i = p.1 := congrArg Prod.fst e
        rw [e1] at hi
        exact (hp hi).elim
      · exact hsupp π hπ hfix i x h hi

/-- **Predicative comprehension along a chain.** For every formula over the chain and every
environment with finitely many non-trivial values, the set of the objects of the level `t 1`
that satisfy the formula is the extension of an object of the level `t 0`. -/
theorem pred {t : ℕ → H.W} {k : ℕ} (hc : T.Chain t k) (hk : 1 ≤ k) {φ : CForm} (hφ : φ.Ok k)
    {ρ : ℕ → ℕ → H.W} (hρ : ∀ i, i ≤ k → ∀ x, ρ i x ∈ T.Tp (t i)) (L : List (ℕ × ℕ))
    (hL : ∀ i x, (i, x) ∉ L → ρ i x = H.op H.emp H.emp) :
    ∃ y, y ∈ T.Tp (t 0) ∧ ∀ z, z ∈ T.Tp (t 1) →
      (H.Mem T.M T.d T.F (t 0) (t 1) z y ↔ T.Sat t φ (upd2 ρ 1 0 z)) := by
  have h0 := hc.top
  have h1 := T.chain_proper hc 1 hk
  have h10 : t 1 ∈ t 0 := (hc.desc 0 (by omega)).1
  obtain ⟨Sp, hfin, htok, hsupp⟩ := T.supp_list hc ρ hρ L
  obtain ⟨X, hX⟩ := H.sep' (T.Tp (t 1)) (fun z => T.Sat t φ (upd2 ρ 1 0 z)) (T.def_sat t φ ρ 1 0)
  have hXT : ∀ z, z ∈ X → z ∈ T.Ts (t 1) := fun z hz => by
    rw [T.Ts_of_ne h1.2]
    exact ((hX z).mp hz).1
  obtain ⟨y, hy, -, hcase⟩ := T.symm_comp h0 (T.hI (t 0)) h10 hXT hfin htok
    (fun π hπ hfix z z' hz hact => by
      obtain ⟨hzT, hsat⟩ := (hX z).mp hz
      obtain ⟨-, hact1⟩ := (T.actN_low hc hπ (i := 0) (by omega)).mp hact
      have hz'T := T.act_mem h1 (T.derN_aut hc hπ 1 hk) hzT hact1
      have hm : T.Moves t k π ρ ρ := fun i hi x => by
        refine ⟨hρ i hi x, ?_⟩
        by_cases hmem : (i, x) ∈ L
        · exact hsupp π hπ hfix i x hmem hi
        · rw [hL i x hmem]
          exact actRaw_emp
      exact (hX z').mpr ⟨hz'T, (T.sat_equi hc hπ φ hφ _ _ (T.moves_upd hm hzT hact1)).mp hsat⟩)
  have hExt : T.Ext (t 0) y (t 1) X := by
    rcases hcase with ⟨hX0, e⟩ | e | ⟨β', X', e, hinv⟩
    · refine ⟨H.emp, H.emp, e, Or.inr ⟨fun h => h1.2 h.symm, fun l => ?_⟩⟩
      rw [hX0]
      exact ⟨fun h => (H.not_mem_emp l h).elim,
        fun ⟨c, S, X', η, x, _, _, hx, _⟩ => (H.not_mem_emp x hx).elim⟩
    · exact ⟨t 1, X, e, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨β', X', e, Or.inr ⟨hinv.2.2.2.1, hinv.2.2.2.2.2.2⟩⟩
  refine ⟨y, hy, fun z hz => ?_⟩
  rw [T.mem_of_ext hExt, hX z]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

end Tower

end Host


/-! ## Unions of partial isomorphisms, and the raise of an automorphism of a lower stage -/

namespace Host

variable {H : Host}

theorem bun_cancel {α β u u' : H.W} (hα : α ∈ H.om) (hβα : β ∈ α) (hu : H.PType u β)
    (hu' : H.PType u' β) (h : H.bun u (H.sg α) = H.bun u' (H.sg α)) : u = u' := by
  have key : ∀ {u u' : H.W}, H.PType u β → H.bun u (H.sg α) = H.bun u' (H.sg α) →
      ∀ x, x ∈ u → x ∈ u' := by
    intro u u' hu h x hx
    have hx' : x ∈ H.bun u' (H.sg α) := by
      rw [← h]
      exact H.mem_bun.mpr (Or.inl hx)
    rcases H.mem_bun.mp hx' with h1 | h1
    · exact h1
    · have h2 := ptype_lt hα hβα hu hx
      rw [H.mem_sg.mp h1] at h2
      exact (H.mem_irrefl _ h2).elim
  exact H.ext' fun x => ⟨key hu h x, key hu' h.symm x⟩

theorem col_raise {M d F α β t u γ δ c S P : H.W} (hα : α ∈ H.om) (hβα : β ∈ α)
    (hu : H.PType u β) (hc : H.Col M d F β (H.op t u) γ δ c S P) :
    H.Col M d F α (H.op t (H.bun u (H.sg α))) γ δ c S (H.bun P (H.sg α)) := by
  have hβ : β ∈ H.om := (H.om_trans α hα β hβα).1
  obtain ⟨hl, hmin, hrest, hP0, hγδ, hγP, hdesc⟩ := col_iff.mp hc
  have hγβ := gamma_lt hβ hu hrest hP0 hγP
  have hγα := H.om_mem_trans hα hβα hγβ
  refine col_iff.mpr ⟨hl, minIs_raise hα hβα hu hmin, rest_raise hα hβα hu hmin hrest,
    fun h0 => H.not_mem_emp α (h0 ▸ H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl))), hγδ,
    fun x hx => ?_, (desc_stage hγβ hγα).mp hdesc⟩
  rcases H.mem_bun.mp hx with hx | hx
  · exact hγP x hx
  · rw [H.mem_sg.mp hx]
    exact hγα

/-- The colour of a raised token comes from the lower stage, unless the token is a label on
the one-element path. -/
theorem col_lower_cases {M d F α β t u γ δ c S P' : H.W} (hα : α ∈ H.om) (hβα : β ∈ α)
    (hβ0 : β ≠ H.emp) (hu : H.PType u β)
    (hc : H.Col M d F α (H.op t (H.bun u (H.sg α))) γ δ c S P') :
    (u = H.sg β ∧ ∃ r ξ X η, t = H.label r ξ X η) ∨
      ∃ P, P' = H.bun P (H.sg α) ∧ H.Col M d F β (H.op t u) γ δ c S P := by
  have hβ : β ∈ H.om := (H.om_trans α hα β hβα).1
  obtain ⟨hl, hmin', hrest', hP'0, hγδ, hγP', hdesc⟩ := col_iff.mp hc
  have hβu : β ∈ u := by
    rcases hu with h | h
    · exact (hβ0 h.2).elim
    · exact h.1
  have hδu : δ ∈ u := by
    rcases H.mem_bun.mp hmin'.1 with h | h
    · exact h
    · exfalso
      have h1 := hmin'.2 β (H.mem_bun.mpr (Or.inl hβu))
      rw [H.mem_sg.mp h] at h1
      rcases H.mem_suc.mp h1 with h2 | h2
      · exact H.mem_asymm h2 hβα
      · rw [h2] at hβα
        exact H.mem_irrefl _ hβα
  have hδα : δ ∈ α := ptype_lt hα hβα hu hδu
  obtain ⟨P, hP⟩ := H.sep' u (fun x => x ≠ δ) (by hdef)
  have hmin : H.MinIs u δ := ⟨hδu, fun x hx => hmin'.2 x (H.mem_bun.mpr (Or.inl hx))⟩
  have eP : P' = H.bun P (H.sg α) := H.ext' fun x => by
    rw [hrest' x, H.mem_bun, H.mem_bun, hP x]
    constructor
    · rintro ⟨h | h, hne⟩
      · exact Or.inl ⟨h, hne⟩
      · exact Or.inr h
    · rintro (⟨h, hne⟩ | h)
      · exact ⟨Or.inl h, hne⟩
      · refine ⟨Or.inr h, fun e => ?_⟩
        rw [H.mem_sg.mp h] at e
        rw [← e] at hδα
        exact H.mem_irrefl _ hδα
  by_cases hP0 : P = H.emp
  · left
    have hall : ∀ x, x ∈ u → x = δ := fun x hx => by
      by_contra hne
      have hxP := (hP x).mpr ⟨hx, hne⟩
      rw [hP0] at hxP
      exact H.not_mem_emp x hxP
    obtain ⟨X, η, e⟩ := hl
    refine ⟨H.ext' fun x => ⟨fun hx => ?_, fun hx => ?_⟩, _, _, X, η, e⟩
    · rw [H.mem_sg, hall x hx, hall β hβu]
    · rw [H.mem_sg.mp hx]
      exact hβu
  · right
    have hγP : ∀ x, x ∈ P → γ ∈ x := fun x hx => hγP' x (by
      rw [eP]
      exact H.mem_bun.mpr (Or.inl hx))
    have hγβ := gamma_lt hβ hu hP hP0 hγP
    exact ⟨P, eP, col_iff.mpr ⟨hl, hmin, hP, hP0, hγδ, hγP,
      (desc_stage hγβ (H.om_mem_trans hα hβα hγβ)).mpr hdesc⟩⟩

/-- **Union of two compatible partial isomorphisms.** -/
theorem piso_bun {M d F α θ₁ θ₂ : H.W} (h₁ : H.PIso M d F α θ₁) (h₂ : H.PIso M d F α θ₂)
    (hf : ∀ v w w', H.App θ₁ v w → H.App θ₂ v w' → w = w')
    (hi : ∀ v v' w, H.App θ₁ v w → H.App θ₂ v' w → v = v')
    (ha1 : ∀ a b p a' b', H.App θ₁ (H.op a p) (H.op a' p) → H.App θ₂ (H.op b p) (H.op b' p) →
      (∃ X η, a = H.atom X η) → (∃ r ξ X η, b = H.label r ξ X η) → (H.Adj a b ↔ H.Adj a' b'))
    (ha2 : ∀ a b p a' b', H.App θ₂ (H.op a p) (H.op a' p) → H.App θ₁ (H.op b p) (H.op b' p) →
      (∃ X η, a = H.atom X η) → (∃ r ξ X η, b = H.label r ξ X η) → (H.Adj a b ↔ H.Adj a' b')) :
    H.PIso M d F α (H.bun θ₁ θ₂) := by
  have happ : ∀ {a b}, H.App (H.bun θ₁ θ₂) a b ↔ H.App θ₁ a b ∨ H.App θ₂ a b := by
    intro a b
    rw [H.app_iff, H.mem_bun]
    exact or_congr H.app_iff.symm H.app_iff.symm
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := id h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := id h₂
  refine ⟨⟨fun p hp => ?_, fun a b b' h h' => ?_⟩, fun v w h => ?_, fun v v' w h h' => ?_,
    fun t p t' p' h => ?_, fun a b p a' b' ha hb hat hl => ?_,
    fun v w γ δ c S P h hc => ?_, fun v w γ δ c S' P h hc => ?_⟩
  · rcases H.mem_bun.mp hp with hp | hp
    · exact a1.1 p hp
    · exact b1.1 p hp
  · rcases happ.mp h with h | h <;> rcases happ.mp h' with h' | h'
    · exact a1.2 _ _ _ h h'
    · exact hf _ _ _ h h'
    · exact (hf _ _ _ h' h).symm
    · exact b1.2 _ _ _ h h'
  · rcases happ.mp h with h | h
    · exact a2 _ _ h
    · exact b2 _ _ h
  · rcases happ.mp h with h | h <;> rcases happ.mp h' with h' | h'
    · exact a3 _ _ _ h h'
    · exact hi _ _ _ h h'
    · exact (hi _ _ _ h' h).symm
    · exact b3 _ _ _ h h'
  · rcases happ.mp h with h | h
    · exact a4 _ _ _ _ h
    · exact b4 _ _ _ _ h
  · rcases happ.mp ha with ha | ha <;> rcases happ.mp hb with hb | hb
    · exact a5 _ _ _ _ _ ha hb hat hl
    · exact ha1 _ _ _ _ _ ha hb hat hl
    · exact ha2 _ _ _ _ _ ha hb hat hl
    · exact b5 _ _ _ _ _ ha hb hat hl
  · rcases happ.mp h with h | h
    · obtain ⟨S', hS', hco⟩ := a6 v w γ δ c S P h hc
      exact ⟨S', hS', fun j t u hj =>
        (hco j t u hj).imp fun t' ht' => ⟨ht'.1, happ.mpr (Or.inl ht'.2)⟩⟩
    · obtain ⟨S', hS', hco⟩ := b6 v w γ δ c S P h hc
      exact ⟨S', hS', fun j t u hj =>
        (hco j t u hj).imp fun t' ht' => ⟨ht'.1, happ.mpr (Or.inr ht'.2)⟩⟩
  · rcases happ.mp h with h | h
    · exact a7 v w γ δ c S' P h hc
    · exact b7 v w γ δ c S' P h hc

/-- The raise to the stage `α` of the restriction of a function `π` on tokens to a set `Tst`
exists as an element of the pool level. -/
theorem exists_raiseR {M Tst π α : H.W} (hM : H.Closed M) (hT : Tst ∈ M) (hα : α ∈ M)
    (hπ : H.IsFun π) (hπM : ∀ a b, H.App π a b → b ∈ M) :
    ∃ R, R ∈ M ∧ (∀ q, q ∈ R → ∃ a b, H.IsOp q a b) ∧
      ∀ a b, H.App R a b ↔ ∃ v u v', H.op v u ∈ Tst ∧ H.App π (H.op v u) (H.op v' u) ∧
        a = H.op v (H.bun u (H.sg α)) ∧ b = H.op v' (H.bun u (H.sg α)) := by
  have hR : Def2 H (fun w q => ∃ v u v', w = H.op v u ∧ H.App π (H.op v u) (H.op v' u) ∧
      q = H.op (H.op v (H.bun u (H.sg α))) (H.op v' (H.bun u (H.sg α)))) := by hdef
  have hfun : ∀ w ∈ Tst, ∀ q q', (∃ v u v', w = H.op v u ∧ H.App π (H.op v u) (H.op v' u) ∧
      q = H.op (H.op v (H.bun u (H.sg α))) (H.op v' (H.bun u (H.sg α)))) →
      (∃ v u v', w = H.op v u ∧ H.App π (H.op v u) (H.op v' u) ∧
      q' = H.op (H.op v (H.bun u (H.sg α))) (H.op v' (H.bun u (H.sg α)))) → q = q' := by
    rintro w - q q' ⟨v, u, v', e, hp, eq⟩ ⟨v2, u2, v2', e2, hp2, eq2⟩
    obtain ⟨e3, e4⟩ := H.op_inj (e.symm.trans e2)
    rw [← e3, ← e4] at hp2
    rw [eq, eq2, ← e3, ← e4, (H.op_inj (hπ.2 _ _ _ hp hp2)).1]
  obtain ⟨g, hgf, hg⟩ : ∃ g, H.IsFun g ∧ ∀ w q, H.App g w q ↔ w ∈ Tst ∧
      ∃ v u v', w = H.op v u ∧ H.App π (H.op v u) (H.op v' u) ∧
        q = H.op (H.op v (H.bun u (H.sg α))) (H.op v' (H.bun u (H.sg α))) :=
    ⟨H.mkFun Tst _ hR hfun, H.isFun_mkFun, fun w q => H.app_mkFun⟩
  have hdom : H.dom g ∈ M := hM.sub _ _ (fun w hw => by
    obtain ⟨q, hq⟩ := H.mem_dom.mp hw
    exact ((hg w q).mp hq).1) hT
  have hval : ∀ w q, H.App g w q → q ∈ M := by
    intro w q hq
    obtain ⟨hw, v, u, v', e, hp, eq⟩ := (hg w q).mp hq
    rw [e] at hw
    obtain ⟨hv, hu⟩ := hM.of_op_mem (hM.trans _ _ hw hT)
    have hv' := (hM.of_op_mem (hπM _ _ hp)).1
    have hua : H.bun u (H.sg α) ∈ M := hM.bun_mem hu (hM.sg_mem hα)
    rw [eq]
    exact hM.op_mem (hM.op_mem hv hua) (hM.op_mem hv' hua)
  refine ⟨H.ran g, hM.ran_mem hgf hdom hval, fun q hq => ?_, fun a b => ?_⟩
  · obtain ⟨w, hw⟩ := H.mem_ran.mp hq
    obtain ⟨-, v, u, v', -, -, eq⟩ := (hg w q).mp hw
    exact ⟨_, _, H.isOp_iff.mpr eq⟩
  · rw [H.app_iff, H.mem_ran]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨hwT, v, u, v', e, hp, eq⟩ := (hg w _).mp hw
      obtain ⟨e1, e2⟩ := H.op_inj eq
      rw [e] at hwT
      exact ⟨v, u, v', hwT, hp, e1, e2⟩
    · rintro ⟨v, u, v', hwT, hp, e1, e2⟩
      exact ⟨H.op v u, (hg _ _).mpr ⟨hwT, v, u, v', rfl, hp, by rw [e1, e2]⟩⟩

/-- **The raise of an automorphism of a lower stage**, restricted to a closed set of tokens
without labels on the one-element path, is a partial isomorphism of the upper stage. -/
theorem piso_raise {M d F α β π Tst R : H.W} (hα : α ∈ H.om) (hαd : α ∈ H.suc d) (hβα : β ∈ α)
    (hβ0 : β ≠ H.emp) (hπ : H.IsAut M d F β π) (hT : ∀ v, v ∈ Tst → H.IsTok M d β v)
    (hcl : ∀ v γ δ c S P j s u, v ∈ Tst → H.Col M d F β v γ δ c S P → H.App S j (H.op s u) →
      H.op s (H.bun u P) ∈ Tst)
    (hQ : ∀ b, H.op b (H.sg β) ∈ Tst → ¬ ∃ r ξ X η, b = H.label r ξ X η)
    (hRp : ∀ q, q ∈ R → ∃ a b, H.IsOp q a b)
    (hR : ∀ a b, H.App R a b ↔ ∃ v u v', H.op v u ∈ Tst ∧ H.App π (H.op v u) (H.op v' u) ∧
      a = H.op v (H.bun u (H.sg α)) ∧ b = H.op v' (H.bun u (H.sg α))) :
    H.PIso M d F α R := by
  obtain ⟨⟨p1, p2, p3, p4, p5, p6, p7⟩, -, -⟩ := id hπ
  have hty : ∀ {v u}, H.op v u ∈ Tst → H.PType u β := by
    intro v u h
    obtain ⟨t0, u0, e, -, hu, -⟩ := hT _ h
    rw [(H.op_inj e).2]
    exact hu
  have hty' : ∀ {v u v'}, H.App π (H.op v u) (H.op v' u) → H.PType u β := by
    intro v u v' h
    obtain ⟨t0, u0, e, -, hu, -⟩ := (p2 _ _ h).1
    rw [(H.op_inj e).2]
    exact hu
  refine ⟨⟨hRp, fun a b b' h h' => ?_⟩, fun x y h => ?_, fun x x' y h h' => ?_,
    fun t p t' p' h => ?_, fun a b p a' b' ha hb hat hl => ?_,
    fun x y γ δ c S P' h hc => ?_, fun x y γ δ c S' P' h hc => ?_⟩
  · obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR a b).mp h
    obtain ⟨v2, u2, v2', hvT2, hp2, e1', e2'⟩ := (hR a b').mp h'
    obtain ⟨e3, e4⟩ := H.op_inj (e1.symm.trans e1')
    have e5 := bun_cancel hα hβα (hty hvT) (hty hvT2) e4
    rw [← e3, ← e5] at hp2
    rw [e2, e2', ← e5, (H.op_inj (p1.2 _ _ _ hp hp2)).1]
  · obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR x y).mp h
    rw [e1, e2]
    exact ⟨tok_raise hα hβα hαd (p2 _ _ hp).1, tok_raise hα hβα hαd (p2 _ _ hp).2⟩
  · obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR x y).mp h
    obtain ⟨v2, u2, v2', hvT2, hp2, e1', e2'⟩ := (hR x' y).mp h'
    obtain ⟨e3, e4⟩ := H.op_inj (e2.symm.trans e2')
    have e5 := bun_cancel hα hβα (hty hvT) (hty hvT2) e4
    rw [← e3, ← e5] at hp2
    rw [e1, e1', ← e5, (H.op_inj (p3 _ _ _ hp hp2)).1]
  · obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR _ _).mp h
    obtain ⟨e3, e4⟩ := H.op_inj e1
    obtain ⟨e5, e6⟩ := H.op_inj e2
    rw [e3, e5, e4, e6]
    exact ⟨rfl, (p4 _ _ _ _ hp).2⟩
  · obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR _ _).mp ha
    obtain ⟨v2, u2, v2', hvT2, hp2, e1', e2'⟩ := (hR _ _).mp hb
    obtain ⟨e3, e4⟩ := H.op_inj e1
    obtain ⟨e5, -⟩ := H.op_inj e2
    obtain ⟨e3', e4'⟩ := H.op_inj e1'
    obtain ⟨e5', -⟩ := H.op_inj e2'
    have e6 := bun_cancel hα hβα (hty hvT) (hty hvT2) (e4.symm.trans e4')
    rw [← e3, ← e5] at hp
    rw [← e3', ← e5', ← e6] at hp2
    exact p5 a b u a' b' hp hp2 hat hl
  · obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR x y).mp h
    rw [e1] at hc
    rcases col_lower_cases hα hβα hβ0 (hty hvT) hc with ⟨eu, hlab⟩ | ⟨P, eP, hcβ⟩
    · rw [eu] at hvT
      exact (hQ v hvT hlab).elim
    · obtain ⟨S', hS', hco⟩ := p6 _ _ γ δ c S P hp hcβ
      rw [e2, eP]
      refine ⟨S', col_raise hα hβα (hty' hp) hS', fun j s w hj => ?_⟩
      obtain ⟨s', hs', hπs⟩ := hco j s w hj
      refine ⟨s', hs', (hR _ _).mpr ⟨s, H.bun w P, s', hcl _ γ δ c S P j s w hvT hcβ hj, hπs, ?_, ?_⟩⟩
      · rw [bun_assoc]
      · rw [bun_assoc]
  · obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR x y).mp h
    rw [e2] at hc
    rcases col_lower_cases hα hβα hβ0 (hty hvT) hc with ⟨eu, hlab⟩ | ⟨P, eP, hcβ⟩
    · rw [eu] at hvT hp
      exact (hQ v hvT ((piso_label hπ.1 hp).mpr hlab)).elim
    · obtain ⟨S, hS⟩ := p7 _ _ γ δ c S' P hp hcβ
      rw [e1, eP]
      exact ⟨S, col_raise hα hβα (hty hvT) hS⟩

end Host


/-! ## Type lowering -/

namespace Host

variable {H : Host}

/-- The chain of two levels. -/
def chain2 (H : Host) (a b : H.W) : ℕ → H.W
  | 0 => a
  | _ => b

namespace Tower

variable (T : Tower H)

theorem chain2_ok {a b : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp) :
    T.Chain (H.chain2 a b) 1 :=
  ⟨ha, fun i hi => by
    have e : i = 0 := by omega
    rw [e]
    exact ⟨hba, hb0⟩⟩

/-- The three cases of symmetric comprehension give the extension. -/
theorem ext_of_cases {a b y X : H.W} (hb0 : b ≠ H.emp)
    (h : (X = H.emp ∧ y = H.op H.emp H.emp) ∨ y = H.op b X ∨
      ∃ β' X', y = H.op β' X' ∧ H.IsInv T.M T.d T.F a b X β' X') : T.Ext a y b X := by
  rcases h with ⟨hX0, e⟩ | e | ⟨β', X', e, hinv⟩
  · refine ⟨H.emp, H.emp, e, Or.inr ⟨fun h => hb0 h.symm, fun l => ?_⟩⟩
    rw [hX0]
    exact ⟨fun h => (H.not_mem_emp l h).elim,
      fun ⟨c, S, X', η, x, _, _, hx, _⟩ => (H.not_mem_emp x hx).elim⟩
  · exact ⟨b, X, e, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨β', X', e, Or.inr ⟨hinv.2.2.2.1, hinv.2.2.2.2.2.2⟩⟩

/-- An object of the level `γ` has a support at the stage `β` above it that contains no token
on the one-element path. -/
theorem supp_raise2 {β γ z : H.W} (hβ : T.Proper β) (hγβ : γ ∈ β) (hγ0 : γ ≠ H.emp)
    (hz : z ∈ T.Tp γ) :
    ∃ Ss, H.Fin Ss ∧ (∀ v, v ∈ Ss → H.IsTok T.M T.d β v) ∧
      (∀ σ, H.IsAut T.M T.d T.F β σ → (∀ v, v ∈ Ss → H.App σ v v) →
        ∀ ρ, H.IsDer σ β γ ρ → H.ActRaw T.F γ ρ z z) ∧
      ∀ b, ¬ H.op b (H.sg β) ∈ Ss := by
  obtain ⟨Ss, hfin, htok, hsupp, hshape⟩ :=
    T.supp_raise (T.chain2_ok hβ hγβ hγ0) (i := 1) (le_refl 1) (x := z) hz
  refine ⟨Ss, hfin, htok, fun σ hσ hfix ρ hρ => ?_, fun b hb => ?_⟩
  · have h := hsupp σ hσ hfix
    have e : T.derN (H.chain2 β γ) σ 1 = H.derS T.M σ β γ := rfl
    rw [e] at h
    rw [der_unique hρ (isDer_derS T.hM (aut_sub T.hM T.hdM hσ.1))]
    exact h
  · obtain ⟨v0, u, e, hu⟩ := hshape _ hb
    have hu' : H.PType u γ := hu
    have hγu : γ ∈ u := hu'.elim (fun h => (hγ0 h.2).elim) (fun h => h.1)
    have h1 : γ ∈ H.sg β := by
      rw [(H.op_inj e).2]
      exact H.mem_bun.mpr (Or.inl hγu)
    have h2 := hγβ
    rw [H.mem_sg.mp h1] at h2
    exact H.mem_irrefl _ h2

/-- The singleton of an object of a lower level, supported by a given support of the object. -/
theorem sing_supp {β γ z Ss : H.W} (hβ : T.Proper β) (hγβ : γ ∈ β) (hγ0 : γ ≠ H.emp)
    (hz : z ∈ T.Tp γ) (hfin : H.Fin Ss) (htok : ∀ v, v ∈ Ss → H.IsTok T.M T.d β v)
    (hfix : ∀ σ, H.IsAut T.M T.d T.F β σ → (∀ v, v ∈ Ss → H.App σ v v) →
      ∀ ρ, H.IsDer σ β γ ρ → H.ActRaw T.F γ ρ z z) :
    ∃ s, s ∈ T.Tp β ∧ H.SuppSet T.F (T.Gs β) β Ss s ∧ T.Ext β s γ (H.sg z) := by
  have hXT : ∀ z', z' ∈ H.sg z → z' ∈ T.Ts γ := fun z' hz' => by
    rw [H.mem_sg.mp hz', T.Ts_of_ne hγ0]
    exact hz
  obtain ⟨s, hs, hsupp, hcase⟩ := T.symm_comp hβ (T.hI β) hγβ hXT hfin htok
    (fun σ hσ hσfix z1 z1' hz1 hact => by
      rw [H.mem_sg.mp hz1] at hact
      obtain ⟨ρ, hρ, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hσ.1) β γ
      obtain ⟨-, hact'⟩ := (T.low_proper hβ (T.invT_all γ (T.lower_proper hβ hγβ hγ0)) hγβ hγ0
        hσ hρ).mp hact
      rw [actRaw_fun hact' (hfix σ hσ hσfix ρ hρ)]
      exact H.mem_sg.mpr rfl)
  exact ⟨s, hs, hsupp, T.ext_of_cases hγ0 hcase⟩

/-- `s` is the singleton, at the stage `b`, of the object `x` of the level `c`. -/
def IsSing (b c x s : H.W) : Prop :=
  s ∈ T.Tp b ∧ ∀ z, z ∈ T.Tp c → (H.Mem T.M T.d T.F b c z s ↔ z = x)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- **Type lowering.** If the set of the singletons (at `β`) of the elements of a set `X` of
objects of the level `γ` is the extension of an object of the stage `α`, then `X` is the
extension of an object of the stage `β`. -/
theorem lower {α β γ y X : H.W} (hα : T.Proper α) (hβα : β ∈ α) (hβ0 : β ≠ H.emp)
    (hγβ : γ ∈ β) (hγ0 : γ ≠ H.emp) (hy : y ∈ T.Tp α) (hX : ∀ z, z ∈ X → z ∈ T.Tp γ)
    (hyX : ∀ s, s ∈ T.Tp β →
      (H.Mem T.M T.d T.F α β s y ↔ ∃ x, x ∈ X ∧ T.IsSing β γ x s)) :
    ∃ w, w ∈ T.Tp β ∧ ∀ z, z ∈ T.Tp γ → (H.Mem T.M T.d T.F β γ z w ↔ z ∈ X) := by
  have hβ := T.lower_proper hα hβα hβ0
  have hαo := T.proper_om hα
  have hβo := T.proper_om hβ
  have hnm : ∀ {a : H.W} v γ δ c S P, v ∈ T.M → H.IsTok T.M T.d a v →
      H.Col T.M T.d T.F a v γ δ c S P → c ∈ T.M :=
    fun v γ δ c S P hvL _ hc => col_name_mem T.hM hvL hc
  -- a closed set of tokens that contains a support of `y`
  obtain ⟨-, β0, D0, -, -, Sp, hfin, htok, hsupp⟩ := ((T.spec hα).2.2.1 y).mp hy
  obtain ⟨θ1, R1, hθ1, -, -, -, hcov1, -, hM1, hF1⟩ :=
    cover (Z := H.emp) T.hM T.hdM T.hM (fun _ h => h) T.hdM T.hM T.hdM T.hM.emp_mem hαo hnm
      Sp hfin (fun v hv => ⟨htok v hv, tok_mem T.hM T.hdM (htok v hv)⟩) H.emp H.emp piso_emp
      T.hM.emp_mem (fun v w h => (H.not_mem_emp _ (H.app_iff.mp h)).elim)
  have hCM : H.dom θ1 ∈ T.M := T.hM.dom_mem (hM1 T.hM.emp_mem)
  -- the tokens of the stage `β` whose raise is in the closed set
  obtain ⟨C', hC'⟩ := H.sep' (H.dom θ1)
    (fun w => ∃ v u, w = H.op v (H.bun u (H.sg α)) ∧ H.PType u β) (by hdef)
  have hC'fin : H.Fin C' :=
    H.fin_sub (fin_dom (hF1 H.fin_emp)) C' (fun w hw => ((hC' w).mp hw).1)
  have hRl : Def2 H (fun w w' => ∃ v u, w = H.op v (H.bun u (H.sg α)) ∧ H.PType u β ∧
      w' = H.op v u) := by hdef
  have hRlf : ∀ w ∈ C', ∀ w' w'', (∃ v u, w = H.op v (H.bun u (H.sg α)) ∧ H.PType u β ∧
      w' = H.op v u) → (∃ v u, w = H.op v (H.bun u (H.sg α)) ∧ H.PType u β ∧ w'' = H.op v u) →
      w' = w'' := by
    rintro w - w' w'' ⟨v, u, e, hu, ew⟩ ⟨v2, u2, e2, hu2, ew2⟩
    obtain ⟨e3, e4⟩ := H.op_inj (e.symm.trans e2)
    rw [ew, ew2, e3, bun_cancel hαo hβα hu hu2 e4]
  obtain ⟨r, hrf, hr⟩ : ∃ r, H.IsFun r ∧ ∀ w w', H.App r w w' ↔ w ∈ C' ∧
      ∃ v u, w = H.op v (H.bun u (H.sg α)) ∧ H.PType u β ∧ w' = H.op v u :=
    ⟨H.mkFun C' _ hRl hRlf, H.isFun_mkFun, fun w w' => H.app_mkFun⟩
  obtain ⟨Sb, hSbfin, hSb⟩ := fin_image hC'fin hrf (fun w hw => by
    obtain ⟨-, v, u, e, hu⟩ := (hC' w).mp hw
    exact ⟨_, (hr _ _).mpr ⟨hw, v, u, e, hu, rfl⟩⟩)
  have hSbmem : ∀ v u, H.PType u β → H.op v (H.bun u (H.sg α)) ∈ H.dom θ1 → H.op v u ∈ Sb :=
    fun v u hu h => (hSb _).mpr ⟨_, (hC' _).mpr ⟨h, v, u, rfl, hu⟩,
      (hr _ _).mpr ⟨(hC' _).mpr ⟨h, v, u, rfl, hu⟩, v, u, rfl, hu, rfl⟩⟩
  have hSbtok : ∀ w', w' ∈ Sb → H.IsTok T.M T.d β w' := fun w' hw' => by
    obtain ⟨w, hw, hww'⟩ := (hSb w').mp hw'
    obtain ⟨-, v, u, e, hu, ew⟩ := (hr _ _).mp hww'
    obtain ⟨w0, hw0⟩ := H.mem_dom.mp ((hC' w).mp hw).1
    have h := (hθ1.2.1 _ _ hw0).1
    rw [e] at h
    rw [ew]
    exact tok_lower hβ0 hu h
  have hXT : ∀ z, z ∈ X → z ∈ T.Ts γ := fun z hz => by
    rw [T.Ts_of_ne hγ0]
    exact hX z hz
  -- the lowered support supports `X`
  have hstab : ∀ π, H.IsAut T.M T.d T.F β π → (∀ v, v ∈ Sb → H.App π v v) →
      ∀ z z', z ∈ X → H.ActLow T.F β π γ z z' → z' ∈ X := by
    intro π hπ hfix z z' hz hact
    have hzT := hX z hz
    obtain ⟨Ss, hSsfin, hSstok, hSsfix, hSsQ⟩ := T.supp_raise2 hβ hγβ hγ0 hzT
    obtain ⟨s, hs, hssupp, hsext⟩ := T.sing_supp hβ hγβ hγ0 hzT hSsfin hSstok hSsfix
    -- a closed set of tokens of the stage `β` that contains the support of the singleton
    obtain ⟨θ2, R2, hθ2, -, -, -, hcov2, hnew2, hM2, -⟩ :=
      cover (Z := H.emp) T.hM T.hdM T.hM (fun _ h => h) T.hdM T.hM T.hdM T.hM.emp_mem hβo hnm
        Ss hSsfin (fun v hv => ⟨hSstok v hv, tok_mem T.hM T.hdM (hSstok v hv)⟩) H.emp H.emp
        piso_emp T.hM.emp_mem (fun v w h => (H.not_mem_emp _ (H.app_iff.mp h)).elim)
    have hTM : H.dom θ2 ∈ T.M := T.hM.dom_mem (hM2 T.hM.emp_mem)
    have hTtok : ∀ v, v ∈ H.dom θ2 → H.IsTok T.M T.d β v := fun v hv => by
      obtain ⟨w, hw⟩ := H.mem_dom.mp hv
      exact (hθ2.2.1 _ _ hw).1
    have hTty : ∀ {v u}, H.op v u ∈ H.dom θ2 → H.PType u β := by
      intro v u h
      obtain ⟨t0, u0, e, -, hu, -⟩ := hTtok _ h
      rw [(H.op_inj e).2]
      exact hu
    have hTcl : ∀ v γ' δ c S P j s' u, v ∈ H.dom θ2 → H.Col T.M T.d T.F β v γ' δ c S P →
        H.App S j (H.op s' u) → H.op s' (H.bun u P) ∈ H.dom θ2 := by
      intro v γ' δ c S P j s' u hv hc hj
      obtain ⟨w, hw⟩ := H.mem_dom.mp hv
      obtain ⟨S', -, hco⟩ := hθ2.2.2.2.2.2.1 v w γ' δ c S P hw hc
      obtain ⟨t', -, ht'⟩ := hco j s' u hj
      exact H.mem_dom.mpr ⟨_, ht'⟩
    have hTQ : ∀ b, H.op b (H.sg β) ∈ H.dom θ2 → ¬ ∃ r ξ X η, b = H.label r ξ X η := by
      intro b hb hlab
      obtain ⟨w, hw⟩ := H.mem_dom.mp hb
      rcases hnew2 _ w hw with h | ⟨-, -, -, hSs | ⟨v0, γ', δ, c, S, P, j, s', u, hc, hj, e⟩⟩
      · exact H.not_mem_emp _ (H.app_iff.mp h)
      · exact hSsQ b hSs
      · obtain ⟨p, X1, η1, -, -, -, hP0, -, hγP, hdesc⟩ := hc
        obtain ⟨e1, e2⟩ := H.op_inj e
        obtain ⟨x, hx⟩ := H.ne_emp hP0
        have hxβ : x = β := H.mem_sg.mp (by
          rw [e2]
          exact H.mem_bun.mpr (Or.inr hx))
        have hγ'β : γ' ∈ β := by
          rw [← hxβ]
          exact hγP x hx
        obtain ⟨s1, u1, es, -, hty, hk⟩ := desc_tok hdesc hj
        obtain ⟨es1, es2⟩ := H.op_inj es
        rw [← es1, ← es2] at hk
        rw [← es2] at hty
        have hu0 : u = H.emp := H.eq_emp fun y hy => by
          have hyβ : y = β := H.mem_sg.mp (by
            rw [e2]
            exact H.mem_bun.mpr (Or.inl hy))
          have h1 := ptype_le hty hy
          rw [hyβ] at h1
          rcases H.mem_suc.mp h1 with h2 | h2
          · exact H.mem_asymm h2 hγ'β
          · rw [h2] at hγ'β
            exact H.mem_irrefl _ hγ'β
        rcases hk with hk | hk
        · obtain ⟨r, ξ, X2, η2, eb⟩ := hlab
          rw [e1] at eb
          exact not_atom_of_label eb hk.2
        · exact hk.2 hu0
    -- the raise of `π` on this closed set, glued with the identity on the first closed set
    obtain ⟨R, hRM, hRp, hR⟩ := exists_raiseR (α := α) T.hM hTM (T.hM.nat_mem hαo) hπ.1.1
      (fun a b hab => tok_mem T.hM T.hdM (hπ.1.2.1 _ _ hab).2)
    have hRpiso := piso_raise hαo hα.1 hβα hβ0 hπ hTtok hTcl hTQ hRp hR
    have hfixC : ∀ v u, H.PType u β → H.op v (H.bun u (H.sg α)) ∈ H.dom θ1 →
        H.App π (H.op v u) (H.op v u) := fun v u hu h => hfix _ (hSbmem v u hu h)
    have hθ : H.PIso T.M T.d T.F α (H.bun (H.idOn (H.dom θ1)) R) := by
      refine piso_bun (piso_id_dom hθ1) hRpiso ?_ ?_ ?_ ?_
      · intro a w w' h h'
        obtain ⟨ha, ew⟩ := app_idOn.mp h
        obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR _ _).mp h'
        rw [e1] at ha
        have ev := (H.op_inj (hπ.1.1.2 _ _ _ hp (hfixC v u (hTty hvT) ha))).1
        rw [ew, e1, e2, ev]
      · intro a a' w h h'
        obtain ⟨ha, ew⟩ := app_idOn.mp h
        obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR _ _).mp h'
        have ea : a = H.op v' (H.bun u (H.sg α)) := ew.symm.trans e2
        rw [ea] at ha
        have ev := (H.op_inj (hπ.1.2.2.1 _ _ _ hp (hfixC v' u (hTty hvT) ha))).1
        rw [ea, e1, ev]
      · intro a b p a' b' h h' hat hl
        obtain ⟨ha, e⟩ := app_idOn.mp h
        obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR _ _).mp h'
        obtain ⟨e3, e4⟩ := H.op_inj e1
        obtain ⟨e5, -⟩ := H.op_inj e2
        rw [e4] at ha
        rw [← e3, ← e5] at hp
        rw [(H.op_inj e).1]
        exact hπ.1.2.2.2.2.1 a b u a b' (hfixC a u (hTty hvT) ha) hp hat hl
      · intro a b p a' b' h h' hat hl
        obtain ⟨v, u, v', hvT, hp, e1, e2⟩ := (hR _ _).mp h
        obtain ⟨hb, e⟩ := app_idOn.mp h'
        obtain ⟨e3, e4⟩ := H.op_inj e1
        obtain ⟨e5, -⟩ := H.op_inj e2
        rw [e4] at hb
        rw [← e3, ← e5] at hp
        rw [(H.op_inj e).1]
        exact hπ.1.2.2.2.2.1 a b u a' b hp (hfixC b u (hTty hvT) hb) hat hl
    have hθM : H.bun (H.idOn (H.dom θ1)) R ∈ T.M := T.hM.bun_mem (T.hM.idOn_mem hCM) hRM
    obtain ⟨πs, hπs, hsubπs, -⟩ := foa T.hM T.hdM hαo hθ hθM
    have happθ : ∀ {a b}, H.App (H.idOn (H.dom θ1)) a b ∨ H.App R a b → H.App πs a b := fun h =>
      H.app_iff.mpr (hsubπs _ (H.mem_bun.mpr (h.imp H.app_iff.mp H.app_iff.mp)))
    have hyfix : H.ActRaw T.F α πs y y := hsupp πs ((T.mem_Gs hα).mpr hπs) (fun v hv => by
      obtain ⟨w', hw'⟩ := hcov1 v hv
      exact happθ (Or.inl (app_idOn.mpr ⟨H.mem_dom.mpr ⟨w', hw'⟩, rfl⟩)))
    -- the derivative of the extension agrees with `π` on the closed set
    obtain ⟨ρs, hρs, -⟩ := exists_der T.hM (aut_sub T.hM T.hdM hπs.1) α β
    have hρsA := der_aut hαo hα.1 hβα hβ0 hπs hρs
    have hagree : ∀ v, v ∈ H.dom θ2 → ∀ w', H.App π v w' → H.App ρs v w' := by
      intro v hv w' hvw
      obtain ⟨t0, u, e, -, hu, -⟩ := hTtok v hv
      rw [e] at hv hvw
      obtain ⟨t', e'⟩ := piso_mid hπ.1 hvw
      rw [e'] at hvw
      rw [e, e']
      exact (der_app hρs).mpr ⟨t0, u, t', rfl, rfl, hu,
        happθ (Or.inr ((hR _ _).mpr ⟨t0, u, t', hv, hvw, rfl, rfl⟩))⟩
    obtain ⟨s2, hs2, hact2⟩ := T.act_fwd hβ hπ hs
    obtain ⟨s1, hs1, hact1⟩ := T.act_fwd hβ hρsA hs
    have e12 : s1 = s2 := by
      have hκ : H.ActRaw T.F β (H.comp (H.inv π) ρs) s s :=
        hssupp _ ((T.mem_Gs hβ).mpr (isAut_comp hρsA (isAut_inv hπ))) (fun v hv => by
          obtain ⟨w', hw'⟩ := hπ.2.1 v (hSstok v hv)
          obtain ⟨w0, hw0⟩ := hcov2 v hv
          exact app_comp.mpr ⟨w', hagree v (H.mem_dom.mpr ⟨w0, hw0⟩) w' hw', app_inv.mpr hw'⟩)
      have hI := T.hI β
      have hspre := T.obj_pre hβ hs
      have hs1pre := T.obj_pre hβ hs1
      obtain ⟨x2, -, hx2⟩ := T.raw_tot hβ hI (isAut_inv hπ) hs1pre
      have e := actRaw_fun (T.raw_comp hβ hI hρsA (isAut_inv hπ) hspre hact1 hx2) hκ
      rw [e] at hx2
      have h3 := T.raw_inv hβ hI (isAut_inv hπ) hs1pre hx2
      rw [inv_inv hπ.1.1.1] at h3
      exact actRaw_fun h3 hact2
    have hsy : H.Mem T.M T.d T.F α β s y :=
      (hyX s hs).mpr ⟨z, hz, hs, fun z0 _ => (T.mem_of_ext hsext).trans H.mem_sg⟩
    have hs1y : H.Mem T.M T.d T.F α β s1 y :=
      (T.mem_equi hα hπs hy hyfix hβα hβ0 hs
        ((T.low_proper hα (T.invT_all β hβ) hβα hβ0 hπs hρs).mpr ⟨hs, hact1⟩)).mp hsy
    rw [e12] at hs1y
    obtain ⟨x', hx', -, hx'sing⟩ := (hyX s2 hs2).mp hs1y
    have hzTs : z ∈ T.Ts γ := by
      rw [T.Ts_of_ne hγ0]
      exact hzT
    have hz'T : z' ∈ T.Tp γ := by
      have h := T.low_mem hβ (T.hI β) hπ hγβ hzTs hact
      rw [T.Ts_of_ne hγ0] at h
      exact h
    have hz's2 : H.Mem T.M T.d T.F β γ z' s2 :=
      (T.mem_equi hβ hπ hs hact2 hγβ hγ0 hzT hact).mp
        ((T.mem_of_ext hsext).mpr (H.mem_sg.mpr rfl))
    rw [(hx'sing z' hz'T).mp hz's2]
    exact hx'
  obtain ⟨w, hw, -, hcase⟩ := T.symm_comp hβ (T.hI β) hγβ hXT hSbfin hSbtok hstab
  have hExt := T.ext_of_cases (a := β) hγ0 hcase
  exact ⟨w, hw, fun z _ => T.mem_of_ext hExt⟩

end Tower

end Host


/-! ## The axioms of the flat model, I: singletons, pairs, Boolean operations -/

namespace Host

variable {H : Host}

/-- The environment whose values are all the empty object. -/
noncomputable def env0 (H : Host) : ℕ → ℕ → H.W := fun _ _ => H.op H.emp H.emp

namespace Tower

variable (T : Tower H)

/-- `p` is the unordered pair, at the stage `a`, of the objects `x`, `y` of the level `b`. -/
def IsUp (a b x y p : H.W) : Prop :=
  p ∈ T.Tp a ∧ ∀ z, z ∈ T.Tp b → (H.Mem T.M T.d T.F a b z p ↔ z = x ∨ z = y)

/-- `p` is the ordered pair, at the stage `a` and formed through the level `b`, of the objects
`x`, `y` of the level `c`. -/
def IsOp (a b c x y p : H.W) : Prop :=
  ∃ s u, T.IsSing b c x s ∧ T.IsUp b c x y u ∧ T.IsUp a b s u p

theorem env0_typed {t : ℕ → H.W} {k : ℕ} (hc : T.Chain t k) :
    ∀ i, i ≤ k → ∀ x, env0 H i x ∈ T.Tp (t i) :=
  fun i hi _ => T.emp_mem_Tp (T.chain_proper hc i hi)

theorem upd2_typed {t : ℕ → H.W} {k j y : ℕ} {v : H.W} {ρ : ℕ → ℕ → H.W}
    (hρ : ∀ i, i ≤ k → ∀ x, ρ i x ∈ T.Tp (t i)) (hv : v ∈ T.Tp (t j)) :
    ∀ i, i ≤ k → ∀ x, upd2 ρ j y v i x ∈ T.Tp (t i) := by
  intro i hi x
  by_cases h : i = j ∧ x = y
  · rw [h.1, h.2, upd2_same]
    exact hv
  · rw [upd2_ne _ _ h]
    exact hρ i hi x

theorem env0_supp : ∀ i x, (i, x) ∉ ([] : List (ℕ × ℕ)) → env0 H i x = H.op H.emp H.emp :=
  fun _ _ _ => rfl

theorem upd2_supp {ρ : ℕ → ℕ → H.W} {L : List (ℕ × ℕ)} {j y : ℕ} {v : H.W}
    (hL : ∀ i x, (i, x) ∉ L → ρ i x = H.op H.emp H.emp) :
    ∀ i x, (i, x) ∉ ((j, y) :: L) → upd2 ρ j y v i x = H.op H.emp H.emp := by
  intro i x h
  have h1 : ¬ (i = j ∧ x = y) := fun e => h (by
    rw [e.1, e.2]
    exact List.mem_cons.mpr (Or.inl rfl))
  rw [upd2_ne _ _ h1]
  exact hL i x (fun hm => h (List.mem_cons.mpr (Or.inr hm)))

section two

variable {a b : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
include ha hba hb0

/-- **Singletons.** -/
theorem sing_ex {x : H.W} (hx : x ∈ T.Tp b) : ∃ s, T.IsSing a b x s := by
  have hc := T.chain2_ok ha hba hb0
  obtain ⟨y, hy, h⟩ := T.pred hc (le_refl 1) (φ := .eq 1 0 1) (le_refl 1)
    (T.upd2_typed (j := 1) (y := 1) (T.env0_typed hc) hx) _ (upd2_supp env0_supp)
  exact ⟨y, hy, fun z hz => (h z hz).trans (by simp [Sat, upd2])⟩

/-- **Unordered pairs.** -/
theorem up_ex {x y : H.W} (hx : x ∈ T.Tp b) (hy : y ∈ T.Tp b) : ∃ p, T.IsUp a b x y p := by
  have hc := T.chain2_ok ha hba hb0
  obtain ⟨p, hp, h⟩ := T.pred hc (le_refl 1) (φ := .or (.eq 1 0 1) (.eq 1 0 2))
    ⟨le_refl 1, le_refl 1⟩
    (T.upd2_typed (j := 1) (y := 2) (T.upd2_typed (j := 1) (y := 1) (T.env0_typed hc) hx) hy) _
    (upd2_supp (upd2_supp env0_supp))
  exact ⟨p, hp, fun z hz => (h z hz).trans (by simp [Sat, upd2])⟩

/-- **Intersections.** -/
theorem inter_ex {x y : H.W} (hx : x ∈ T.Tp a) (hy : y ∈ T.Tp a) :
    ∃ w, w ∈ T.Tp a ∧ ∀ z, z ∈ T.Tp b →
      (H.Mem T.M T.d T.F a b z w ↔ H.Mem T.M T.d T.F a b z x ∧ H.Mem T.M T.d T.F a b z y) := by
  have hc := T.chain2_ok ha hba hb0
  obtain ⟨w, hw, h⟩ := T.pred hc (le_refl 1) (φ := .and (.mem 0 0 1) (.mem 0 0 2))
    ⟨le_refl 1, le_refl 1⟩
    (T.upd2_typed (j := 0) (y := 2) (T.upd2_typed (j := 0) (y := 1) (T.env0_typed hc) hx) hy) _
    (upd2_supp (upd2_supp env0_supp))
  exact ⟨w, hw, fun z hz => (h z hz).trans (by simp [Sat, upd2, chain2])⟩

/-- **Complements.** -/
theorem compl_ex {x : H.W} (hx : x ∈ T.Tp a) :
    ∃ w, w ∈ T.Tp a ∧ ∀ z, z ∈ T.Tp b →
      (H.Mem T.M T.d T.F a b z w ↔ ¬ H.Mem T.M T.d T.F a b z x) := by
  have hc := T.chain2_ok ha hba hb0
  obtain ⟨w, hw, h⟩ := T.pred hc (le_refl 1) (φ := .neg (.mem 0 0 1)) (le_refl 1)
    (T.upd2_typed (j := 0) (y := 1) (T.env0_typed hc) hx) _ (upd2_supp env0_supp)
  exact ⟨w, hw, fun z hz => (h z hz).trans (by simp [Sat, upd2, chain2])⟩

/-- **Extensionality**, for all objects of a stage and every proper lower level. -/
theorem ext_ax {x y : H.W} (hx : x ∈ T.Tp a) (hy : y ∈ T.Tp a)
    (h : ∀ z, z ∈ T.Tp b → (H.Mem T.M T.d T.F a b z x ↔ H.Mem T.M T.d T.F a b z y)) : x = y :=
  T.ext_full ha hx hy hba hb0 h

end two

end Tower

end Host


/-! ## The axioms of the flat model, II: Kuratowski pairs and four comprehension axioms -/

namespace Host

variable {H : Host}

/-- The chain given by a list of levels. -/
noncomputable def chainL (H : Host) (l : List H.W) (i : ℕ) : H.W := l.getD i H.emp

/-- `s` (index `i`) is the singleton of `x` (index `i+1`); `V` is a bound name. -/
def fSing (i s x V : ℕ) : CForm := .all (i + 1) V (.iff (.mem i V s) (.eq (i + 1) V x))

/-- `p` (index `i`) is the unordered pair of `x`, `y` (index `i+1`). -/
def fUp (i p x y V : ℕ) : CForm :=
  .all (i + 1) V (.iff (.mem i V p) (.or (.eq (i + 1) V x) (.eq (i + 1) V y)))

/-- `p` (index `i`) is the ordered pair of `x`, `y` (index `i+2`). -/
def fOp (i p x y S U V : ℕ) : CForm :=
  .ex (i + 1) S (.ex (i + 1) U
    (.and (fSing (i + 1) S x V) (.and (fUp (i + 1) U x y V) (fUp i p S U V))))

namespace Tower

variable (T : Tower H)

theorem chain3_ok {a b c : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp) (hcb : c ∈ b)
    (hc0 : c ≠ H.emp) : T.Chain (H.chainL [a, b, c]) 2 :=
  ⟨ha, fun i hi => by
    rcases i with _ | _ | i
    · exact ⟨hba, hb0⟩
    · exact ⟨hcb, hc0⟩
    · omega⟩

theorem chain4_ok {a b c d : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp) (hcb : c ∈ b)
    (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) : T.Chain (H.chainL [a, b, c, d]) 3 :=
  ⟨ha, fun i hi => by
    rcases i with _ | _ | _ | i
    · exact ⟨hba, hb0⟩
    · exact ⟨hcb, hc0⟩
    · exact ⟨hdc, hd0⟩
    · omega⟩

theorem chain5_ok {a b c d e : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) (hed : e ∈ d)
    (he0 : e ≠ H.emp) : T.Chain (H.chainL [a, b, c, d, e]) 4 :=
  ⟨ha, fun i hi => by
    rcases i with _ | _ | _ | _ | i
    · exact ⟨hba, hb0⟩
    · exact ⟨hcb, hc0⟩
    · exact ⟨hdc, hd0⟩
    · exact ⟨hed, he0⟩
    · omega⟩

theorem sat_fSing (t : ℕ → H.W) (ρ : ℕ → ℕ → H.W) (i s x V : ℕ) (hV : V ≠ x) :
    T.Sat t (fSing i s x V) ρ ↔ ∀ v, v ∈ T.Tp (t (i + 1)) →
      (H.Mem T.M T.d T.F (t i) (t (i + 1)) v (ρ i s) ↔ v = ρ (i + 1) x) := by
  show (∀ v, v ∈ T.Tp (t (i + 1)) → (H.Mem T.M T.d T.F (t i) (t (i + 1))
      (upd2 ρ (i + 1) V v (i + 1) V) (upd2 ρ (i + 1) V v i s) ↔
      upd2 ρ (i + 1) V v (i + 1) V = upd2 ρ (i + 1) V v (i + 1) x)) ↔ _
  refine forall_congr' fun v => imp_congr Iff.rfl ?_
  rw [upd2_same, upd2_ne _ _ (show ¬ (i = i + 1 ∧ s = V) by omega),
    upd2_ne _ _ (show ¬ (i + 1 = i + 1 ∧ x = V) from fun h => hV h.2.symm)]

theorem sat_fUp (t : ℕ → H.W) (ρ : ℕ → ℕ → H.W) (i p x y V : ℕ) (hVx : V ≠ x) (hVy : V ≠ y) :
    T.Sat t (fUp i p x y V) ρ ↔ ∀ v, v ∈ T.Tp (t (i + 1)) →
      (H.Mem T.M T.d T.F (t i) (t (i + 1)) v (ρ i p) ↔ v = ρ (i + 1) x ∨ v = ρ (i + 1) y) := by
  show (∀ v, v ∈ T.Tp (t (i + 1)) → (H.Mem T.M T.d T.F (t i) (t (i + 1))
      (upd2 ρ (i + 1) V v (i + 1) V) (upd2 ρ (i + 1) V v i p) ↔
      upd2 ρ (i + 1) V v (i + 1) V = upd2 ρ (i + 1) V v (i + 1) x ∨
        upd2 ρ (i + 1) V v (i + 1) V = upd2 ρ (i + 1) V v (i + 1) y)) ↔ _
  refine forall_congr' fun v => imp_congr Iff.rfl ?_
  simp only [upd2_same, upd2_ne _ _ (show ¬ (i = i + 1 ∧ p = V) by omega),
    upd2_ne _ _ (show ¬ (i + 1 = i + 1 ∧ x = V) from fun h => hVx h.2.symm),
    upd2_ne _ _ (show ¬ (i + 1 = i + 1 ∧ y = V) from fun h => hVy h.2.symm)]

theorem sat_fOp (t : ℕ → H.W) (ρ : ℕ → ℕ → H.W) (i p x y S U V : ℕ) (hSU : S ≠ U) (hVx : V ≠ x)
    (hVy : V ≠ y) (hVS : V ≠ S) (hVU : V ≠ U) (hp : ρ i p ∈ T.Tp (t i)) :
    T.Sat t (fOp i p x y S U V) ρ ↔
      T.IsOp (t i) (t (i + 1)) (t (i + 1 + 1)) (ρ (i + 1 + 1) x) (ρ (i + 1 + 1) y) (ρ i p) := by
  show (∃ s, s ∈ T.Tp (t (i + 1)) ∧ ∃ u, u ∈ T.Tp (t (i + 1)) ∧
    (T.Sat t (fSing (i + 1) S x V) (upd2 (upd2 ρ (i + 1) S s) (i + 1) U u) ∧
     T.Sat t (fUp (i + 1) U x y V) (upd2 (upd2 ρ (i + 1) S s) (i + 1) U u) ∧
     T.Sat t (fUp i p S U V) (upd2 (upd2 ρ (i + 1) S s) (i + 1) U u))) ↔ _
  have e1 : ∀ s u, upd2 (upd2 ρ (i + 1) S s) (i + 1) U u (i + 1) S = s := fun s u => by
    rw [upd2_ne _ _ (show ¬ (i + 1 = i + 1 ∧ S = U) from fun h => hSU h.2), upd2_same]
  have e2 : ∀ s u, upd2 (upd2 ρ (i + 1) S s) (i + 1) U u (i + 1) U = u :=
    fun s u => upd2_same _ _ _ _
  have e3 : ∀ s u z, upd2 (upd2 ρ (i + 1) S s) (i + 1) U u (i + 1 + 1) z = ρ (i + 1 + 1) z :=
    fun s u z => by
      rw [upd2_ne _ _ (show ¬ (i + 1 + 1 = i + 1 ∧ z = U) by omega),
        upd2_ne _ _ (show ¬ (i + 1 + 1 = i + 1 ∧ z = S) by omega)]
  have e4 : ∀ s u, upd2 (upd2 ρ (i + 1) S s) (i + 1) U u i p = ρ i p := fun s u => by
    rw [upd2_ne _ _ (show ¬ (i = i + 1 ∧ p = U) by omega),
      upd2_ne _ _ (show ¬ (i = i + 1 ∧ p = S) by omega)]
  constructor
  · rintro ⟨s, hs, u, hu, h1, h2, h3⟩
    rw [T.sat_fSing _ _ _ _ _ _ hVx] at h1
    rw [T.sat_fUp _ _ _ _ _ _ _ hVx hVy] at h2
    rw [T.sat_fUp _ _ _ _ _ _ _ hVS hVU] at h3
    simp only [e1, e2, e3, e4] at h1 h2 h3
    exact ⟨s, u, ⟨hs, h1⟩, ⟨hu, h2⟩, ⟨hp, h3⟩⟩
  · rintro ⟨s, u, ⟨hs, h1⟩, ⟨hu, h2⟩, ⟨-, h3⟩⟩
    refine ⟨s, hs, u, hu, ?_, ?_, ?_⟩
    · rw [T.sat_fSing _ _ _ _ _ _ hVx]
      simp only [e1, e3]
      exact h1
    · rw [T.sat_fUp _ _ _ _ _ _ _ hVx hVy]
      simp only [e2, e3]
      exact h2
    · rw [T.sat_fUp _ _ _ _ _ _ _ hVS hVU]
      simp only [e1, e2, e4]
      exact h3

section kuratowski

variable {a b : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
include ha hba hb0

theorem sing_unique {x s s' : H.W} (h : T.IsSing a b x s) (h' : T.IsSing a b x s') : s = s' :=
  T.ext_full ha h.1 h'.1 hba hb0 fun z hz => (h.2 z hz).trans (h'.2 z hz).symm

theorem up_unique {x y p p' : H.W} (h : T.IsUp a b x y p) (h' : T.IsUp a b x y p') : p = p' :=
  T.ext_full ha h.1 h'.1 hba hb0 fun z hz => (h.2 z hz).trans (h'.2 z hz).symm

end kuratowski

theorem sing_inj {a b x x' s : H.W} (hx : x ∈ T.Tp b) (h : T.IsSing a b x s)
    (h' : T.IsSing a b x' s) : x = x' :=
  (h'.2 x hx).mp ((h.2 x hx).mpr rfl)

theorem op_unique {a b c x y p p' : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) (h : T.IsOp a b c x y p) (h' : T.IsOp a b c x y p') :
    p = p' := by
  have hb := T.lower_proper ha hba hb0
  obtain ⟨s, u, hs, hu, hp⟩ := h
  obtain ⟨s', u', hs', hu', hp'⟩ := h'
  rw [← T.sing_unique hb hcb hc0 hs hs', ← T.up_unique hb hcb hc0 hu hu'] at hp'
  exact T.up_unique ha hba hb0 hp hp'

/-- **Ordered pairs are injective.** -/
theorem op_inj' {a b c x y x' y' p : H.W} (hx : x ∈ T.Tp c) (hy : y ∈ T.Tp c)
    (hx' : x' ∈ T.Tp c) (hy' : y' ∈ T.Tp c) (h : T.IsOp a b c x y p)
    (h' : T.IsOp a b c x' y' p) : x = x' ∧ y = y' := by
  obtain ⟨s, u, hs, hu, hp⟩ := h
  obtain ⟨s', u', hs', hu', hp'⟩ := h'
  have h1 : s = s' ∨ s = u' := (hp'.2 s hs.1).mp ((hp.2 s hs.1).mpr (Or.inl rfl))
  have h2 : u = s' ∨ u = u' := (hp'.2 u hu.1).mp ((hp.2 u hu.1).mpr (Or.inr rfl))
  have h4 : u' = s ∨ u' = u := (hp.2 u' hu'.1).mp ((hp'.2 u' hu'.1).mpr (Or.inr rfl))
  have mx := hs.2
  have mu := hu.2
  have mx' := hs'.2
  have mu' := hu'.2
  have exx : x = x' := by
    rcases h1 with e | e
    · have hm := (mx x hx).mpr rfl
      rw [e] at hm
      exact (mx' x hx).mp hm
    · have hm := (mu' x' hx').mpr (Or.inl rfl)
      rw [← e] at hm
      exact ((mx x' hx').mp hm).symm
  refine ⟨exx, ?_⟩
  rcases h2 with e | e
  · have hy1 : y = x' := by
      have hm := (mu y hy).mpr (Or.inr rfl)
      rw [e] at hm
      exact (mx' y hy).mp hm
    rcases h4 with e4 | e4
    · have hy'1 : y' = x := by
        have hm := (mu' y' hy').mpr (Or.inr rfl)
        rw [e4] at hm
        exact (mx y' hy').mp hm
      rw [hy1, hy'1, exx]
    · have hy'1 : y' = x' := by
        have hm := (mu' y' hy').mpr (Or.inr rfl)
        rw [e4, e] at hm
        exact (mx' y' hy').mp hm
      rw [hy1, hy'1]
  · have hm := (mu y hy).mpr (Or.inr rfl)
    rw [e] at hm
    rcases (mu' y hy).mp hm with e5 | e5
    · have hm' := (mu' y' hy').mpr (Or.inr rfl)
      rw [← e] at hm'
      rcases (mu y' hy').mp hm' with e6 | e6
      · rw [e5, e6, exx]
      · exact e6.symm
    · exact e5

/-- **The set of all singletons.** -/
theorem cardinalOne_ex {a b c : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) :
    ∃ y, y ∈ T.Tp a ∧ ∀ p, p ∈ T.Tp b →
      (H.Mem T.M T.d T.F a b p y ↔ ∃ q, q ∈ T.Tp c ∧ T.IsSing b c q p) := by
  have hc := T.chain3_ok ha hba hb0 hcb hc0
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega) (φ := .ex 2 1 (fSing 1 0 1 9))
    (by simp [CForm.Ok, fSing]) (T.env0_typed hc) _ env0_supp
  refine ⟨y, hy, fun p hp => (h p hp).trans ?_⟩
  simp only [Sat]
  refine exists_congr fun q => and_congr Iff.rfl ?_
  rw [T.sat_fSing _ _ 1 0 1 9 (by decide)]
  simp [upd2, chainL, IsSing, hp]

/-- **Cross product with the universe.** -/
theorem vCross_ex {a b c d x : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) (hx : x ∈ T.Tp c) :
    ∃ y, y ∈ T.Tp a ∧ ∀ p, p ∈ T.Tp b →
      (H.Mem T.M T.d T.F a b p y ↔ ∃ q, q ∈ T.Tp d ∧ ∃ r, r ∈ T.Tp d ∧
        (T.IsOp b c d q r p ∧ H.Mem T.M T.d T.F c d r x)) := by
  have hc := T.chain4_ok ha hba hb0 hcb hc0 hdc hd0
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega)
    (φ := .ex 3 1 (.ex 3 2 (.and (fOp 1 0 1 2 10 11 12) (.mem 2 2 1))))
    (by simp [CForm.Ok, fSing, fUp, fOp])
    (T.upd2_typed (j := 2) (y := 1) (T.env0_typed hc) hx) _ (upd2_supp env0_supp)
  refine ⟨y, hy, fun p hp => (h p hp).trans ?_⟩
  simp only [Sat]
  refine exists_congr fun q => and_congr Iff.rfl
    (exists_congr fun r => and_congr Iff.rfl (and_congr ?_ ?_))
  · rw [T.sat_fOp _ _ 1 0 1 2 10 11 12 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simpa [upd2, chainL] using hp)]
    simp [upd2, chainL]
  · simp [upd2, chainL]

end Tower

end Host


/-! ## The axioms of the flat model, III: converse, subset, singleton image -/

namespace Host

variable {H : Host}

namespace Tower

variable (T : Tower H)

theorem op_mem_Tp {a b c x y p : H.W} (h : T.IsOp a b c x y p) : p ∈ T.Tp a := by
  obtain ⟨s, u, -, -, hup⟩ := h
  exact hup.1

/-- **Converse.** -/
theorem converse_ex {a b c d x : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) (hx : x ∈ T.Tp a) :
    ∃ y, y ∈ T.Tp a ∧ ∀ p q r r', p ∈ T.Tp d → q ∈ T.Tp d → T.IsOp b c d p q r →
      T.IsOp b c d q p r' → (H.Mem T.M T.d T.F a b r y ↔ H.Mem T.M T.d T.F a b r' x) := by
  have hc := T.chain4_ok ha hba hb0 hcb hc0 hdc hd0
  have hb := T.lower_proper ha hba hb0
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega)
    (φ := .ex 3 1 (.ex 3 2 (.ex 1 3 (.and (fOp 1 0 1 2 10 11 12)
      (.and (fOp 1 3 2 1 10 11 12) (.mem 0 3 1))))))
    (by simp [CForm.Ok, fSing, fUp, fOp])
    (T.upd2_typed (j := 0) (y := 1) (T.env0_typed hc) hx) _ (upd2_supp env0_supp)
  have key : ∀ r, r ∈ T.Tp b → (H.Mem T.M T.d T.F a b r y ↔
      ∃ p, p ∈ T.Tp d ∧ ∃ q, q ∈ T.Tp d ∧ ∃ r', r' ∈ T.Tp b ∧
        (T.IsOp b c d p q r ∧ T.IsOp b c d q p r' ∧ H.Mem T.M T.d T.F a b r' x)) := by
    intro r hr
    refine (h r hr).trans ?_
    simp only [Sat]
    refine exists_congr fun p => and_congr Iff.rfl (exists_congr fun q => and_congr Iff.rfl
      (exists_congr fun r' => and_congr_right fun hr' => and_congr ?_ (and_congr ?_ ?_)))
    · rw [T.sat_fOp _ _ 1 0 1 2 10 11 12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simpa [upd2, chainL] using hr)]
      simp [upd2, chainL]
    · rw [T.sat_fOp _ _ 1 3 2 1 10 11 12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simpa [upd2, chainL] using hr')]
      simp [upd2, chainL]
    · simp [upd2, chainL]
  refine ⟨y, hy, fun p q r r' hp hq hr hr' => ?_⟩
  rw [key r (T.op_mem_Tp hr)]
  constructor
  · rintro ⟨p', hp', q', hq', r'', -, h1, h2, h3⟩
    obtain ⟨e1, e2⟩ := T.op_inj' hp hq hp' hq' hr h1
    rw [← e1, ← e2] at h2
    rw [T.op_unique hb hcb hc0 hdc hd0 hr' h2]
    exact h3
  · intro h3
    exact ⟨p, hp, q, hq, r', T.op_mem_Tp hr', hr, hr', h3⟩

/-- **The inclusion relation.** -/
theorem subset_ex {a b c d e : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) (hed : e ∈ d)
    (he0 : e ≠ H.emp) :
    ∃ y, y ∈ T.Tp a ∧ ∀ p q o, p ∈ T.Tp d → q ∈ T.Tp d → T.IsOp b c d p q o →
      (H.Mem T.M T.d T.F a b o y ↔
        ∀ r, r ∈ T.Tp e → H.Mem T.M T.d T.F d e r p → H.Mem T.M T.d T.F d e r q) := by
  have hc := T.chain5_ok ha hba hb0 hcb hc0 hdc hd0 hed he0
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega)
    (φ := .ex 3 1 (.ex 3 2 (.and (fOp 1 0 1 2 10 11 12)
      (.all 4 1 (.imp (.mem 3 1 1) (.mem 3 1 2))))))
    (by simp [CForm.Ok, fSing, fUp, fOp]) (T.env0_typed hc) _ env0_supp
  have key : ∀ o, o ∈ T.Tp b → (H.Mem T.M T.d T.F a b o y ↔
      ∃ p, p ∈ T.Tp d ∧ ∃ q, q ∈ T.Tp d ∧ (T.IsOp b c d p q o ∧
        ∀ r, r ∈ T.Tp e → H.Mem T.M T.d T.F d e r p → H.Mem T.M T.d T.F d e r q)) := by
    intro o ho
    refine (h o ho).trans ?_
    simp only [Sat]
    refine exists_congr fun p => and_congr Iff.rfl (exists_congr fun q => and_congr Iff.rfl
      (and_congr ?_ ?_))
    · rw [T.sat_fOp _ _ 1 0 1 2 10 11 12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simpa [upd2, chainL] using ho)]
      simp [upd2, chainL]
    · simp [upd2, chainL]
  refine ⟨y, hy, fun p q o hp hq ho => ?_⟩
  rw [key o (T.op_mem_Tp ho)]
  constructor
  · rintro ⟨p', hp', q', hq', h1, h2⟩
    obtain ⟨e1, e2⟩ := T.op_inj' hp hq hp' hq' ho h1
    rw [e1, e2]
    exact h2
  · intro h2
    exact ⟨p, hp, q, hq, ho, h2⟩

/-- **Singleton image.** -/
theorem singletonImage_ex {a b c d e x : H.W} (ha : T.Proper a) (hba : b ∈ a)
    (hb0 : b ≠ H.emp) (hcb : c ∈ b) (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp)
    (hed : e ∈ d) (he0 : e ≠ H.emp) (hx : x ∈ T.Tp b) :
    ∃ y, y ∈ T.Tp a ∧ ∀ z w sz sw P Q, z ∈ T.Tp e → w ∈ T.Tp e → T.IsSing d e z sz →
      T.IsSing d e w sw → T.IsOp b c d sz sw P → T.IsOp c d e z w Q →
      (H.Mem T.M T.d T.F a b P y ↔ H.Mem T.M T.d T.F b c Q x) := by
  have hc := T.chain5_ok ha hba hb0 hcb hc0 hdc hd0 hed he0
  have hb := T.lower_proper ha hba hb0
  have hcP := T.lower_proper hb hcb hc0
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega)
    (φ := .ex 4 1 (.ex 4 2 (.ex 3 3 (.ex 3 4 (.ex 2 5 (.and (fSing 3 3 1 12)
      (.and (fSing 3 4 2 12) (.and (fOp 1 0 3 4 10 11 12)
        (.and (fOp 2 5 1 2 10 11 12) (.mem 1 5 1))))))))))
    (by simp [CForm.Ok, fSing, fUp, fOp])
    (T.upd2_typed (j := 1) (y := 1) (T.env0_typed hc) hx) _ (upd2_supp env0_supp)
  have key : ∀ P, P ∈ T.Tp b → (H.Mem T.M T.d T.F a b P y ↔
      ∃ z, z ∈ T.Tp e ∧ ∃ w, w ∈ T.Tp e ∧ ∃ sz, sz ∈ T.Tp d ∧ ∃ sw, sw ∈ T.Tp d ∧
        ∃ Q, Q ∈ T.Tp c ∧ (T.IsSing d e z sz ∧ T.IsSing d e w sw ∧ T.IsOp b c d sz sw P ∧
          T.IsOp c d e z w Q ∧ H.Mem T.M T.d T.F b c Q x)) := by
    intro P hP
    refine (h P hP).trans ?_
    simp only [Sat]
    refine exists_congr fun z => and_congr Iff.rfl (exists_congr fun w => and_congr Iff.rfl
      (exists_congr fun sz => and_congr_right fun hsz => exists_congr fun sw =>
        and_congr_right fun hsw => exists_congr fun Q => and_congr_right fun hQ =>
          and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))))
    · rw [T.sat_fSing _ _ 3 3 1 12 (by decide)]
      simp only [IsSing]
      have hsz' : sz ∈ T.Tp d := hsz
      simp [upd2, chainL, hsz']
    · rw [T.sat_fSing _ _ 3 4 2 12 (by decide)]
      simp only [IsSing]
      have hsw' : sw ∈ T.Tp d := hsw
      simp [upd2, chainL, hsw']
    · rw [T.sat_fOp _ _ 1 0 3 4 10 11 12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simpa [upd2, chainL] using hP)]
      simp [upd2, chainL]
    · rw [T.sat_fOp _ _ 2 5 1 2 10 11 12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simpa [upd2, chainL] using hQ)]
      simp [upd2, chainL]
    · simp [upd2, chainL]
  refine ⟨y, hy, fun z w sz sw P Q hz hw hsz hsw hP hQ => ?_⟩
  rw [key P (T.op_mem_Tp hP)]
  constructor
  · rintro ⟨z', hz', w', hw', sz', hsz'T, sw', hsw'T, Q', -, h1, h2, h3, h4, h5⟩
    obtain ⟨e1, e2⟩ := T.op_inj' hsz.1 hsw.1 hsz'T hsw'T hP h3
    rw [← e1] at h1
    rw [← e2] at h2
    rw [← T.sing_inj hz hsz h1, ← T.sing_inj hw hsw h2] at h4
    rw [T.op_unique hcP hdc hd0 hed he0 hQ h4]
    exact h5
  · intro h5
    exact ⟨z, hz, w, hw, sz, hsz.1, sw, hsw.1, Q, T.op_mem_Tp hQ, hsz, hsw, hP, hQ, h5⟩

end Tower

end Host


/-! ## The axioms of the flat model, IV: the two insertions -/

namespace Host

variable {H : Host}

namespace Tower

variable (T : Tower H)

theorem chain6_ok {a b c d e f : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) (hed : e ∈ d)
    (he0 : e ≠ H.emp) (hfe : f ∈ e) (hf0 : f ≠ H.emp) :
    T.Chain (H.chainL [a, b, c, d, e, f]) 5 :=
  ⟨ha, fun i hi => by
    rcases i with _ | _ | _ | _ | _ | i
    · exact ⟨hba, hb0⟩
    · exact ⟨hcb, hc0⟩
    · exact ⟨hdc, hd0⟩
    · exact ⟨hed, he0⟩
    · exact ⟨hfe, hf0⟩
    · omega⟩

section six

variable {a b c d e f x : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp) (hcb : c ∈ b)
  (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) (hed : e ∈ d) (he0 : e ≠ H.emp)
  (hfe : f ∈ e) (hf0 : f ≠ H.emp) (hx : x ∈ T.Tp c)
include ha hba hb0 hcb hc0 hdc hd0 hed he0 hfe hf0 hx

/-- The common part of the two insertion axioms; `n` is the name of the second component of
the pair on the right-hand side (`3` for `r`, `2` for `q`). -/
theorem insertion_key (n : ℕ) (hn : n = 2 ∨ n = 3) :
    ∃ y, y ∈ T.Tp a ∧ ∀ P, P ∈ T.Tp b → (H.Mem T.M T.d T.F a b P y ↔
      ∃ p, p ∈ T.Tp f ∧ ∃ q, q ∈ T.Tp f ∧ ∃ r, r ∈ T.Tp f ∧ ∃ sp, sp ∈ T.Tp e ∧
        ∃ ssp, ssp ∈ T.Tp d ∧ ∃ oqr, oqr ∈ T.Tp d ∧ ∃ o, o ∈ T.Tp d ∧
          (T.IsSing e f p sp ∧ T.IsSing d e sp ssp ∧ T.IsOp d e f q r oqr ∧
            T.IsOp b c d ssp oqr P ∧ T.IsOp d e f p (if n = 3 then r else q) o ∧
            H.Mem T.M T.d T.F c d o x)) := by
  have hc := T.chain6_ok ha hba hb0 hcb hc0 hdc hd0 hed he0 hfe hf0
  have hn12 : (12 : ℕ) ≠ n := by
    rcases hn with h | h <;> rw [h] <;> decide
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega)
    (φ := .ex 5 1 (.ex 5 2 (.ex 5 3 (.ex 4 4 (.ex 3 5 (.ex 3 6 (.ex 3 7
      (.and (fSing 4 4 1 12) (.and (fSing 3 5 4 12) (.and (fOp 3 6 2 3 10 11 12)
        (.and (fOp 1 0 5 6 10 11 12) (.and (fOp 3 7 1 n 10 11 12) (.mem 2 7 1)))))))))))))
    (by simp [CForm.Ok, fSing, fUp, fOp])
    (T.upd2_typed (j := 2) (y := 1) (T.env0_typed hc) hx) _ (upd2_supp env0_supp)
  refine ⟨y, hy, fun P hP => (h P hP).trans ?_⟩
  simp only [Sat]
  refine exists_congr fun p => and_congr Iff.rfl (exists_congr fun q => and_congr Iff.rfl
    (exists_congr fun r => and_congr Iff.rfl (exists_congr fun sp => and_congr_right fun hsp =>
      exists_congr fun ssp => and_congr_right fun hssp => exists_congr fun oqr =>
        and_congr_right fun hoqr => exists_congr fun o => and_congr_right fun ho =>
          and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))))))
  · rw [T.sat_fSing _ _ 4 4 1 12 (by decide)]
    simp only [IsSing]
    have hsp' : sp ∈ T.Tp e := hsp
    simp [upd2, chainL, hsp']
  · rw [T.sat_fSing _ _ 3 5 4 12 (by decide)]
    simp only [IsSing]
    have hssp' : ssp ∈ T.Tp d := hssp
    simp [upd2, chainL, hssp']
  · rw [T.sat_fOp _ _ 3 6 2 3 10 11 12 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simpa [upd2, chainL] using hoqr)]
    simp [upd2, chainL]
  · rw [T.sat_fOp _ _ 1 0 5 6 10 11 12 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simpa [upd2, chainL] using hP)]
    simp [upd2, chainL]
  · rw [T.sat_fOp _ _ 3 7 1 n 10 11 12 (by decide) (by decide) hn12 (by decide)
      (by decide) (by simpa [upd2, chainL] using ho)]
    rcases hn with h | h <;> simp [upd2, chainL, h]
  · simp [upd2, chainL]

omit ha hba hb0 hcb hc0 hdc hd0 hed he0 hfe hf0 hx in
/-- The injectivity argument that is common to the two insertion axioms. -/
theorem insertion_match {p q r sp ssp oqr P p' q' r' sp' ssp' oqr' : H.W} (hp : p ∈ T.Tp f)
    (hq : q ∈ T.Tp f) (hr : r ∈ T.Tp f) (hq' : q' ∈ T.Tp f) (hr' : r' ∈ T.Tp f)
    (hssp'T : ssp' ∈ T.Tp d) (hoqr'T : oqr' ∈ T.Tp d)
    (hsp : T.IsSing e f p sp) (hssp : T.IsSing d e sp ssp) (hoqr : T.IsOp d e f q r oqr)
    (hP : T.IsOp b c d ssp oqr P) (h1 : T.IsSing e f p' sp') (h2 : T.IsSing d e sp' ssp')
    (h3 : T.IsOp d e f q' r' oqr') (h4 : T.IsOp b c d ssp' oqr' P) :
    p = p' ∧ q = q' ∧ r = r' := by
  obtain ⟨e1, e2⟩ := T.op_inj' hssp.1 (T.op_mem_Tp hoqr) hssp'T hoqr'T hP h4
  rw [← e1] at h2
  rw [← e2] at h3
  have es : sp = sp' := T.sing_inj hsp.1 hssp h2
  rw [← es] at h1
  obtain ⟨eq, er⟩ := T.op_inj' hq hr hq' hr' hoqr h3
  exact ⟨T.sing_inj hp hsp h1, eq, er⟩

/-- **Insertion two.** -/
theorem insertion2_ex :
    ∃ y, y ∈ T.Tp a ∧ ∀ p q r sp ssp oqr P opr, p ∈ T.Tp f → q ∈ T.Tp f → r ∈ T.Tp f →
      T.IsSing e f p sp → T.IsSing d e sp ssp → T.IsOp d e f q r oqr → T.IsOp b c d ssp oqr P →
      T.IsOp d e f p r opr → (H.Mem T.M T.d T.F a b P y ↔ H.Mem T.M T.d T.F c d opr x) := by
  have hdP := T.lower_proper (T.lower_proper (T.lower_proper ha hba hb0) hcb hc0) hdc hd0
  obtain ⟨y, hy, key⟩ := T.insertion_key ha hba hb0 hcb hc0 hdc hd0 hed he0 hfe hf0 hx 3
    (Or.inr rfl)
  refine ⟨y, hy, fun p q r sp ssp oqr P opr hp hq hr hsp hssp hoqr hP hopr => ?_⟩
  rw [key P (T.op_mem_Tp hP)]
  constructor
  · rintro ⟨p', hp', q', hq', r', hr', sp', -, ssp', hssp'T, oqr', hoqr'T, o, -, h1, h2, h3, h4,
      h5, h6⟩
    obtain ⟨ep, -, er⟩ := T.insertion_match hp hq hr hq' hr' hssp'T hoqr'T hsp hssp hoqr hP h1 h2
      h3 h4
    rw [ite_eq_left rfl, ← ep, ← er] at h5
    rw [T.op_unique hdP hed he0 hfe hf0 hopr h5]
    exact h6
  · intro h6
    exact ⟨p, hp, q, hq, r, hr, sp, hsp.1, ssp, hssp.1, oqr, T.op_mem_Tp hoqr, opr,
      T.op_mem_Tp hopr, hsp, hssp, hoqr, hP, by rw [ite_eq_left rfl]; exact hopr, h6⟩

/-- **Insertion three.** -/
theorem insertion3_ex :
    ∃ y, y ∈ T.Tp a ∧ ∀ p q r sp ssp oqr P opq, p ∈ T.Tp f → q ∈ T.Tp f → r ∈ T.Tp f →
      T.IsSing e f p sp → T.IsSing d e sp ssp → T.IsOp d e f q r oqr → T.IsOp b c d ssp oqr P →
      T.IsOp d e f p q opq → (H.Mem T.M T.d T.F a b P y ↔ H.Mem T.M T.d T.F c d opq x) := by
  have hdP := T.lower_proper (T.lower_proper (T.lower_proper ha hba hb0) hcb hc0) hdc hd0
  obtain ⟨y, hy, key⟩ := T.insertion_key ha hba hb0 hcb hc0 hdc hd0 hed he0 hfe hf0 hx 2
    (Or.inl rfl)
  refine ⟨y, hy, fun p q r sp ssp oqr P opq hp hq hr hsp hssp hoqr hP hopq => ?_⟩
  rw [key P (T.op_mem_Tp hP)]
  constructor
  · rintro ⟨p', hp', q', hq', r', hr', sp', -, ssp', hssp'T, oqr', hoqr'T, o, -, h1, h2, h3, h4,
      h5, h6⟩
    obtain ⟨ep, eq, -⟩ := T.insertion_match hp hq hr hq' hr' hssp'T hoqr'T hsp hssp hoqr hP h1 h2
      h3 h4
    rw [ite_eq_right (by decide), ← ep, ← eq] at h5
    rw [T.op_unique hdP hed he0 hfe hf0 hopq h5]
    exact h6
  · intro h6
    exact ⟨p, hp, q, hq, r, hr, sp, hsp.1, ssp, hssp.1, oqr, T.op_mem_Tp hoqr, opq,
      T.op_mem_Tp hopq, hsp, hssp, hoqr, hP, by rw [ite_eq_right (by decide)]; exact hopq, h6⟩

end six

end Tower

end Host


/-! ## The axioms of the flat model, V: type lowering -/

namespace Host

variable {H : Host}

theorem Def1.congr {P Q : H.W → Prop} (h : Def1 H P) (hPQ : ∀ a, P a ↔ Q a) : Def1 H Q := by
  obtain ⟨φ, ρ, x, hφ, h⟩ := h
  exact ⟨φ, ρ, x, hφ, fun a => (hPQ a).symm.trans (h a)⟩

/-- The formula "for all `q`, `sp`, `P`: if `sp` is the singleton of `p` and `P` is the pair
`(q, sp)`, then `P ∈ x`"; `p` is the variable `(4, 1)` and `x` is the variable `(0, 1)`. -/
def fLow : CForm :=
  .all 3 4 (.all 3 5 (.all 1 6
    (.imp (fSing 3 5 1 12) (.imp (fOp 1 6 4 5 10 11 12) (.mem 0 6 1)))))

namespace Tower

variable (T : Tower H)

theorem sat_fLow {a b c d e x : H.W} (ρ : ℕ → ℕ → H.W) (p : H.W) (h1 : ρ 0 1 = x)
    (h2 : ρ 4 1 = p) :
    T.Sat (H.chainL [a, b, c, d, e]) fLow ρ ↔
      ∀ q, q ∈ T.Tp d → ∀ sp, sp ∈ T.Tp d → ∀ P, P ∈ T.Tp b → T.IsSing d e p sp →
        T.IsOp b c d q sp P → H.Mem T.M T.d T.F a b P x := by
  unfold fLow
  simp only [Sat]
  refine forall_congr' fun q => forall_congr' fun hq => forall_congr' fun sp =>
    forall_congr' fun hsp => forall_congr' fun P => forall_congr' fun hP =>
      imp_congr ?_ (imp_congr ?_ ?_)
  · rw [T.sat_fSing _ _ 3 5 1 12 (by decide)]
    simp only [IsSing]
    have hsp' : sp ∈ T.Tp d := hsp
    simp [upd2, chainL, hsp', h2]
  · rw [T.sat_fOp _ _ 1 6 4 5 10 11 12 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simpa [upd2, chainL] using hP)]
    simp [upd2, chainL]
  · simp [upd2, chainL, h1]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- **Type lowering**, in the form of the axiom of the flat model. -/
theorem typeLower_ex {a b c d e x : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) (hdc : d ∈ c) (hd0 : d ≠ H.emp) (hed : e ∈ d)
    (he0 : e ≠ H.emp) (hx : x ∈ T.Tp a) :
    ∃ y, y ∈ T.Tp d ∧ ∀ p, p ∈ T.Tp e → (H.Mem T.M T.d T.F d e p y ↔
      ∀ q sp P, q ∈ T.Tp d → T.IsSing d e p sp → T.IsOp b c d q sp P →
        H.Mem T.M T.d T.F a b P x) := by
  have hc := T.chain5_ok ha hba hb0 hcb hc0 hdc hd0 hed he0
  have hbP := T.lower_proper ha hba hb0
  have hcP := T.lower_proper hbP hcb hc0
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : H.W → Prop, ∀ p, Φ p ↔ ∀ q, q ∈ T.Tp d → ∀ sp, sp ∈ T.Tp d →
      ∀ P, P ∈ T.Tp b → T.IsSing d e p sp → T.IsOp b c d q sp P → H.Mem T.M T.d T.F a b P x :=
    ⟨_, fun _ => Iff.rfl⟩
  have hρ0 := T.upd2_typed (j := 0) (y := 1) (T.env0_typed hc) hx
  have hΦdef : Def1 H Φ :=
    Def1.congr (T.def_sat (H.chainL [a, b, c, d, e]) fLow (upd2 (env0 H) 0 1 x) 4 1) (fun p =>
      (T.sat_fLow _ p (by simp [upd2]) (by simp [upd2])).trans (hΦ p).symm)
  -- the set of the triple singletons of the wanted elements, at the top level
  obtain ⟨W, hW, hWm⟩ := T.pred hc (by omega)
    (φ := .ex 4 1 (.ex 3 2 (.ex 2 3 (.and (fSing 3 2 1 12) (.and (fSing 2 3 2 12)
      (.and (fSing 1 0 3 12) fLow))))))
    (by simp [CForm.Ok, fSing, fUp, fOp, fLow]) hρ0 _ (upd2_supp env0_supp)
  have keyW : ∀ s3, s3 ∈ T.Tp b → (H.Mem T.M T.d T.F a b s3 W ↔
      ∃ p, p ∈ T.Tp e ∧ ∃ s1, s1 ∈ T.Tp d ∧ ∃ s2, s2 ∈ T.Tp c ∧
        (T.IsSing d e p s1 ∧ T.IsSing c d s1 s2 ∧ T.IsSing b c s2 s3 ∧ Φ p)) := by
    intro s3 hs3
    refine (hWm s3 hs3).trans ?_
    simp only [Sat]
    refine exists_congr fun p => and_congr Iff.rfl (exists_congr fun s1 =>
      and_congr_right fun hs1 => exists_congr fun s2 => and_congr_right fun hs2 =>
        and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
    · rw [T.sat_fSing _ _ 3 2 1 12 (by decide)]
      simp only [IsSing]
      have hs1' : s1 ∈ T.Tp d := hs1
      simp [upd2, chainL, hs1']
    · rw [T.sat_fSing _ _ 2 3 2 12 (by decide)]
      simp only [IsSing]
      have hs2' : s2 ∈ T.Tp c := hs2
      simp [upd2, chainL, hs2']
    · rw [T.sat_fSing _ _ 1 0 3 12 (by decide)]
      simp only [IsSing]
      simp [upd2, chainL, hs3]
    · exact (T.sat_fLow _ p (by simp [upd2]) (by simp [upd2])).trans (hΦ p).symm
  obtain ⟨X3, hX3⟩ := H.sep' (T.Tp e) Φ hΦdef
  obtain ⟨X2, hX2⟩ := H.sep' (T.Tp d) (fun s1 => ∃ p, p ∈ T.Tp e ∧ T.IsSing d e p s1 ∧ Φ p)
    (by hdef)
  obtain ⟨X1, hX1⟩ := H.sep' (T.Tp c) (fun s2 => ∃ s1, s1 ∈ X2 ∧ T.IsSing c d s1 s2) (by hdef)
  -- three lowerings
  obtain ⟨w1, hw1, hw1m⟩ := T.lower ha hba hb0 hcb hc0 hW (fun z hz => ((hX1 z).mp hz).1)
    (fun s hs => by
      rw [keyW s hs]
      constructor
      · rintro ⟨p, hp, s1, hs1, s2, hs2, h1, h2, h3, h4⟩
        exact ⟨s2, (hX1 s2).mpr ⟨hs2, s1, (hX2 s1).mpr ⟨hs1, p, hp, h1, h4⟩, h2⟩, h3⟩
      · rintro ⟨s2, hs2X, h3⟩
        obtain ⟨hs2, s1, hs1X, h2⟩ := (hX1 s2).mp hs2X
        obtain ⟨hs1, p, hp, h1, h4⟩ := (hX2 s1).mp hs1X
        exact ⟨p, hp, s1, hs1, s2, hs2, h1, h2, h3, h4⟩)
  obtain ⟨w2, hw2, hw2m⟩ := T.lower hbP hcb hc0 hdc hd0 hw1 (fun z hz => ((hX2 z).mp hz).1)
    (fun s hs => by
      rw [hw1m s hs, hX1 s]
      exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩)
  obtain ⟨w3, hw3, hw3m⟩ := T.lower hcP hdc hd0 hed he0 hw2 (fun z hz => ((hX3 z).mp hz).1)
    (fun s hs => by
      rw [hw2m s hs, hX2 s]
      constructor
      · rintro ⟨-, p, hp, h1, h4⟩
        exact ⟨p, (hX3 p).mpr ⟨hp, h4⟩, h1⟩
      · rintro ⟨p, hpX, h1⟩
        obtain ⟨hp, h4⟩ := (hX3 p).mp hpX
        exact ⟨hs, p, hp, h1, h4⟩)
  refine ⟨w3, hw3, fun p hp => ?_⟩
  rw [hw3m p hp, hX3 p, hΦ p]
  constructor
  · rintro ⟨-, h⟩ q sp P hq hsp hP
    exact h q hq sp hsp.1 P (T.op_mem_Tp hP) hsp hP
  · intro h
    exact ⟨hp, fun q hq sp _ P _ hsp hP => h q sp P hq hsp hP⟩

end Tower

end Host

/-! ## Hosts from weaker data; closed levels and towers from their characteristic properties -/

/-- The data of a host in which the least-element principle is assumed only for sets, and every
initial segment of the order is included in a set. Collection is assumed only for two
different variables. -/
structure PreHost where
  W : Type
  mem : W → W → Prop
  lt : W → W → Prop
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  pair : ∀ x y, ∃ p, ∀ z, mem z p ↔ z = x ∨ z = y
  union : ∀ x, ∃ u, ∀ z, mem z u ↔ ∃ y, mem y x ∧ mem z y
  inf : ∃ w, (∃ e, mem e w ∧ ∀ z, ¬ mem z e) ∧
    ∀ x, mem x w → ∃ s, mem s w ∧ ∀ z, mem z s ↔ mem z x ∨ z = x
  sep : ∀ (φ : Form), φ.Pure → ∀ (ρ : ℕ → W) (x : ℕ) (a : W),
    ∃ b, ∀ y, mem y b ↔ mem y a ∧ Holds mem lt noRel φ (upd ρ x y)
  coll : ∀ (φ : Form), φ.Pure → ∀ (ρ : ℕ → W) (x y : ℕ) (a : W), x ≠ y →
    (∀ u, mem u a → ∃ v, Holds mem lt noRel φ (upd (upd ρ x u) y v)) →
    ∃ b, ∀ u, mem u a → ∃ v, mem v b ∧ Holds mem lt noRel φ (upd (upd ρ x u) y v)
  lt_irrefl : ∀ x, ¬ lt x x
  lt_trans : ∀ x y z, lt x y → lt y z → lt x z
  lt_tri : ∀ x y, lt x y ∨ x = y ∨ lt y x
  least : ∀ a, (∃ x, mem x a) → ∃ m, mem m a ∧ ∀ b, mem b a → ¬ lt b m
  mem_lt : ∀ x y, mem x y → lt x y
  cover : ∀ a, ∃ T, ∀ b, lt b a → mem b T

theorem upd_upd_same {W : Type} (ρ : ℕ → W) (x : ℕ) (a b : W) : upd (upd ρ x a) x b = upd ρ x b := by
  funext n
  by_cases h : n = x
  · subst h
    simp [upd_same]
  · simp [upd_ne _ _ h]

/-- The host given by the weaker data. -/
def PreHost.toHost (K : PreHost) : Host where
  W := K.W
  mem := K.mem
  lt := K.lt
  ext := K.ext
  pair := K.pair
  union := K.union
  inf := K.inf
  sep := K.sep
  coll := by
    intro φ hφ ρ x y a h
    by_cases hxy : x = y
    · subst hxy
      by_cases hne : ∃ u, K.mem u a
      · obtain ⟨u, hu⟩ := hne
        obtain ⟨v, hv⟩ := h u hu
        obtain ⟨b, hb⟩ := K.pair v v
        refine ⟨b, fun u' hu' => ⟨v, (hb v).mpr (Or.inl rfl), ?_⟩⟩
        rw [upd_upd_same] at hv ⊢
        exact hv
      · exact ⟨a, fun u hu => (hne ⟨u, hu⟩).elim⟩
    · exact K.coll φ hφ ρ x y a hxy h
  lt_irrefl := K.lt_irrefl
  lt_trans := K.lt_trans
  lt_tri := K.lt_tri
  lt_least := by
    intro φ hφ ρ x a ha
    obtain ⟨T, hT⟩ := K.cover a
    obtain ⟨s, hs⟩ := K.sep φ hφ ρ x T
    have ha_least : (∀ b, K.lt b a → ¬ K.mem b s) →
        ∃ m, Holds K.mem K.lt noRel φ (upd ρ x m) ∧
          ∀ b, K.lt b m → ¬ Holds K.mem K.lt noRel φ (upd ρ x b) :=
      fun hno => ⟨a, ha, fun b hb hφb => hno b hb ((hs b).mpr ⟨hT b hb, hφb⟩)⟩
    by_cases hne : ∃ y, K.mem y s
    · obtain ⟨m, hm, hmin⟩ := K.least s hne
      rcases K.lt_tri m a with hma | hma | hma
      · exact ⟨m, ((hs m).mp hm).2, fun b hb hφb =>
          hmin b ((hs b).mpr ⟨hT b (K.lt_trans _ _ _ hb hma), hφb⟩) hb⟩
      · exact ha_least (fun b hb hbs => hmin b hbs (by rw [hma]; exact hb))
      · exact ha_least (fun b hb hbs => hmin b hbs (K.lt_trans _ _ _ hb hma))
    · exact ha_least (fun b _ hbs => hne ⟨b, hbs⟩)
  mem_lt := K.mem_lt

namespace Host

variable {H : Host}

/-- A transitive set that is closed under subsets, bounds every definable relation from one of
its elements into it, includes every initial segment of the order below one of its elements in
one of its elements, and has `ω` as an element, is a closed level. -/
theorem closed_of {K : H.W} (trans : ∀ x y, x ∈ y → y ∈ K → x ∈ K)
    (sub : ∀ x y, H.Sub x y → y ∈ K → x ∈ K)
    (kcoll : ∀ R : H.W → H.W → Prop, Def2 H R → ∀ a, a ∈ K → (∀ u, u ∈ a → ∃ v, v ∈ K ∧ R u v) →
      ∃ b, b ∈ K ∧ ∀ u, u ∈ a → ∃ v, v ∈ b ∧ R u v)
    (cover : ∀ a, a ∈ K → ∃ T, T ∈ K ∧ ∀ b, H.lt b a → b ∈ T)
    (om_mem : H.om ∈ K) : H.Closed K where
  trans := trans
  sub := sub
  bd := by
    intro f hf hd hv
    obtain ⟨b, hb, hb'⟩ := kcoll (fun u v => H.App f u v) (by hdef) (H.dom f) hd
      (fun u hu => by
        obtain ⟨v, hv'⟩ := H.mem_dom.mp hu
        exact ⟨v, hv u v hv', hv'⟩)
    refine ⟨b, hb, fun a' b' hab => ?_⟩
    obtain ⟨v, hvb, hv'⟩ := hb' a' (H.mem_dom.mpr ⟨b', hab⟩)
    rw [hf.2 a' b' v hab hv']
    exact hvb
  seg := by
    intro a ha
    obtain ⟨T, hT, hcov⟩ := cover a ha
    obtain ⟨s, hs⟩ := H.sep' T (fun y => H.lt y a) (by hdef)
    refine ⟨s, sub s T (fun z hz => ((hs z).mp hz).1) hT, fun y => ?_⟩
    rw [hs y]
    exact ⟨fun h => ⟨trans y T h.1 hT, h.2⟩, fun h => ⟨hcov y h.2, h.2⟩⟩
  om_mem := om_mem

/-- A ladder of closed levels of length `d + 1` gives a tower of height `d`. -/
theorem exists_tower (d Λ : H.W) (hd : d ∈ H.om) (hd0 : d ≠ H.emp) (hΛ : H.IsFun Λ)
    (lev : ∀ α, α ∈ H.suc (H.suc d) → α ≠ H.emp → ∃ La, H.App Λ α La ∧ H.Closed La)
    (mono : ∀ α β La Lb, H.App Λ α La → H.App Λ β Lb → α ∈ β → La ∈ Lb) :
    ∃ T : Tower H, T.d = d ∧ T.Λ = Λ := by
  obtain ⟨M, hM, hMc⟩ := lev d (H.mem_suc.mpr (Or.inl (H.mem_suc.mpr (Or.inr rfl)))) hd0
  obtain ⟨Mp, hMp, hMpc⟩ := lev (H.suc d) (H.mem_suc.mpr (Or.inr rfl)) (H.suc_ne_emp d)
  obtain ⟨F, hF⟩ := H.exists_good M Mp d Λ d hd
  exact ⟨{ d := d, Λ := Λ, M := M, Mp := Mp, F := F, hd := hd, hΛ := hΛ, lev := lev, mono := mono,
           hM := hMc, hMp := hMpc, hMd := fun _ => hM, hMpd := hMp,
           hMMp := mono d (H.suc d) M Mp hM hMp (H.mem_suc.mpr (Or.inr rfl)), good := hF }, rfl, rfl⟩

end Host

/-! ## Ladders: from consecutive levels to a tower -/

namespace Host

variable {H : Host}

/-- An inductive set all of whose members are `∅` or successors of members is `ω`. -/
theorem om_eq_of_ind {K : H.W} (hind : H.Ind K)
    (hcases : ∀ x, x ∈ K → x = H.emp ∨ ∃ y, y ∈ K ∧ x = H.suc y) : K = H.om := by
  refine H.ext' fun z => ⟨fun hz => ?_, fun hz => H.mem_om.mp hz K hind⟩
  by_contra hzo
  obtain ⟨m, ⟨hmK, hmo⟩, hmin⟩ := H.least' (fun x => x ∈ K ∧ ¬ x ∈ H.om) (by hdef) ⟨hz, hzo⟩
  rcases hcases m hmK with e | ⟨y, hyK, e⟩
  · exact hmo (e ▸ H.emp_mem_om)
  · have hy : y ∈ m := by rw [e]; exact H.mem_suc.mpr (Or.inr rfl)
    have hyo : y ∈ H.om := by
      by_contra hyo
      exact hmin y (H.mem_lt y m hy) ⟨hyK, hyo⟩
    exact hmo (e ▸ H.suc_mem_om hyo)

/-- In a ladder whose consecutive levels are members of each other and whose levels are
transitive, lower levels are members of higher levels. -/
theorem ladder_mono {Λ : H.W} (hΛ : H.IsFun Λ)
    (hdom : ∀ n Lb, n ∈ H.om → H.App Λ (H.suc n) Lb → ∃ La, H.App Λ n La)
    (hcons : ∀ n La Lb, n ∈ H.om → H.App Λ n La → H.App Λ (H.suc n) Lb → La ∈ Lb)
    (htr : ∀ α La, H.App Λ α La → ∀ x y, x ∈ y → y ∈ La → x ∈ La) :
    ∀ β, β ∈ H.om → ∀ α La Lb, H.App Λ α La → H.App Λ β Lb → α ∈ β → La ∈ Lb := by
  refine H.om_ind (fun β => ∀ α La Lb, H.App Λ α La → H.App Λ β Lb → α ∈ β → La ∈ Lb) (by hdef)
    (fun α La Lb _ _ h => (H.not_mem_emp α h).elim) (fun n hn ih α La Lb hα hβ hαβ => ?_)
  obtain ⟨La0, hLa0⟩ := hdom n Lb hn hβ
  have h0 := hcons n La0 Lb hn hLa0 hβ
  rcases H.mem_suc.mp hαβ with h | h
  · exact htr (H.suc n) Lb hβ La La0 (ih α La La0 hα hLa0 h) h0
  · rw [h] at hα
    rw [hΛ.2 n La La0 hα hLa0]
    exact h0

/-- **A tower from a ladder.** Let `Λ` be a function defined exactly on the numbers up to
`d + 1`, with transitive values, each a member of the next. If the values at the numbers
other than `0` are closed under subsets, bound the definable relations from their elements
into them, and cover the initial segments of the order below their elements, and if `ω` is a
member of the value at `1`, then there is a tower of height `d` with the ladder `Λ`. -/
theorem tower_of_ladder (d Λ : H.W) (hd : d ∈ H.om) (hd0 : d ≠ H.emp) (hΛ : H.IsFun Λ)
    (dom : ∀ α, α ∈ H.suc (H.suc d) → ∃ La, H.App Λ α La)
    (dom' : ∀ α La, H.App Λ α La → α ∈ H.suc (H.suc d))
    (cons : ∀ n La Lb, H.App Λ n La → H.App Λ (H.suc n) Lb → La ∈ Lb)
    (tr : ∀ α La, H.App Λ α La → ∀ x y, x ∈ y → y ∈ La → x ∈ La)
    (om1 : ∀ L1, H.App Λ (H.suc H.emp) L1 → H.om ∈ L1)
    (sub : ∀ α La, H.App Λ α La → α ≠ H.emp → ∀ x y, H.Sub x y → y ∈ La → x ∈ La)
    (kcoll : ∀ α La, H.App Λ α La → α ≠ H.emp → ∀ R : H.W → H.W → Prop, Def2 H R →
      ∀ a, a ∈ La → (∀ u, u ∈ a → ∃ v, v ∈ La ∧ R u v) → ∃ b, b ∈ La ∧ ∀ u, u ∈ a → ∃ v, v ∈ b ∧ R u v)
    (cover : ∀ α La, H.App Λ α La → α ≠ H.emp → ∀ a, a ∈ La → ∃ T, T ∈ La ∧ ∀ b, H.lt b a → b ∈ T) :
    ∃ T : Tower H, T.d = d ∧ T.Λ = Λ := by
  have hsd : H.suc (H.suc d) ∈ H.om := H.suc_mem_om (H.suc_mem_om hd)
  have hnum : ∀ α, α ∈ H.suc (H.suc d) → α ∈ H.om := fun α h => H.mem_om_of_mem hsd h
  have hdown : ∀ α β, β ∈ H.suc (H.suc d) → α ∈ β → α ∈ H.suc (H.suc d) :=
    fun α β hβ hα => (H.om_trans _ hsd β hβ).2 α hα
  have mono : ∀ α β La Lb, H.App Λ α La → H.App Λ β Lb → α ∈ β → La ∈ Lb := by
    intro α β La Lb hα hβ hαβ
    exact H.ladder_mono hΛ
      (fun n Lb _ h => dom n (hdown n _ (dom' _ _ h) (H.mem_suc.mpr (Or.inr rfl))))
      (fun n La Lb _ h1 h2 => cons n La Lb h1 h2) tr β (hnum β (dom' β Lb hβ)) α La Lb hα hβ hαβ
  have omL : ∀ α La, H.App Λ α La → α ≠ H.emp → H.om ∈ La := by
    intro α La hα hα0
    have hαo := hnum α (dom' α La hα)
    rcases H.om_cases hαo with e | ⟨n, hn, e⟩
    · exact (hα0 e).elim
    · by_cases hn0 : n = H.emp
      · rw [e, hn0] at hα
        exact om1 La hα
      · have h1 : H.suc H.emp ∈ α := by
          rw [e]
          have h0 : H.emp ∈ n := by
            rcases H.om_tri H.emp H.emp_mem_om n hn with h | h | h
            · exact h
            · exact (hn0 h.symm).elim
            · exact (H.not_mem_emp n h).elim
          rcases H.suc_mem_or n hn H.emp h0 with h | h
          · exact H.mem_suc.mpr (Or.inl h)
          · exact H.mem_suc.mpr (Or.inr h)
        obtain ⟨L1, hL1⟩ := dom (H.suc H.emp) (hdown _ α (dom' α La hα) h1)
        exact tr α La hα H.om L1 (om1 L1 hL1) (mono _ _ L1 La hL1 hα h1)
  exact H.exists_tower d Λ hd hd0 hΛ
    (fun α hα hα0 => by
      obtain ⟨La, hLa⟩ := dom α hα
      exact ⟨La, hLa, H.closed_of (tr α La hLa) (sub α La hLa hα0) (kcoll α La hLa hα0)
        (cover α La hLa hα0) (omL α La hLa hα0)⟩)
    mono

end Host

