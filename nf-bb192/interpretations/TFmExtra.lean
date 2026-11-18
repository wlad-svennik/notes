import NFUJensenModel

set_option autoImplicit false

/-!
# Typed formulas: satisfaction with typed quantifiers, and derived connectives

`JensenNFU.TFm` (in `NFUJensenModel.lean`) is a syntax of formulas whose quantifiers carry a
type, and `TFm.Strat Γ φ` says that `φ` is well typed when its free variables have the types
listed in `Γ`. This file adds

* `TFm.SatT ty mem φ v`: satisfaction in a structure with a membership relation `mem` and a
  predicate `ty t` for each type `t`, where a quantifier of type `t` ranges over the objects that
  satisfy `ty t`. The environment `v` is a function on `ℕ`;
* disjunction, implication, equivalence and the existential quantifier as abbreviations;
* `TFm.infFm k`: "the universe of type `k` is not finite".

Only Mathlib is used.
-/

namespace JensenNFU

namespace TFm

/-- Extend an environment by a new first value. -/
def scons {α : Type*} (a : α) (v : ℕ → α) : ℕ → α
  | 0 => a
  | i + 1 => v i

@[simp] lemma scons_zero {α : Type*} (a : α) (v : ℕ → α) : scons a v 0 = a := rfl

@[simp] lemma scons_succ {α : Type*} (a : α) (v : ℕ → α) (i : ℕ) : scons a v (i + 1) = v i := rfl

/-- Satisfaction with typed quantifiers: a quantifier of type `t` ranges over `{a | ty t a}`. -/
def SatT {M : Type*} (ty : ℕ → M → Prop) (mem : M → M → Prop) : TFm → (ℕ → M) → Prop
  | .mem i j, v => mem (v i) (v j)
  | .eq i j, v => v i = v j
  | .neg φ, v => ¬SatT ty mem φ v
  | .and φ ψ, v => SatT ty mem φ v ∧ SatT ty mem ψ v
  | .all t φ, v => ∀ a, ty t a → SatT ty mem φ (scons a v)

/-- Disjunction. -/
def or (φ ψ : TFm) : TFm := .neg (.and (.neg φ) (.neg ψ))

/-- Implication. -/
def imp (φ ψ : TFm) : TFm := .neg (.and φ (.neg ψ))

/-- Equivalence. -/
def iff (φ ψ : TFm) : TFm := .and (imp φ ψ) (imp ψ φ)

/-- The existential quantifier over the type `t`. -/
def ex (t : ℕ) (φ : TFm) : TFm := .neg (.all t (.neg φ))

section

variable {M : Type*} {ty : ℕ → M → Prop} {mem : M → M → Prop} {φ ψ : TFm} {v : ℕ → M}

@[simp] lemma satT_mem {i j : ℕ} : SatT ty mem (.mem i j) v ↔ mem (v i) (v j) := Iff.rfl

@[simp] lemma satT_eq {i j : ℕ} : SatT ty mem (.eq i j) v ↔ v i = v j := Iff.rfl

@[simp] lemma satT_neg : SatT ty mem (.neg φ) v ↔ ¬SatT ty mem φ v := Iff.rfl

@[simp] lemma satT_and : SatT ty mem (.and φ ψ) v ↔ SatT ty mem φ v ∧ SatT ty mem ψ v := Iff.rfl

@[simp] lemma satT_all {t : ℕ} :
    SatT ty mem (.all t φ) v ↔ ∀ a, ty t a → SatT ty mem φ (scons a v) := Iff.rfl

@[simp] lemma satT_or : SatT ty mem (or φ ψ) v ↔ SatT ty mem φ v ∨ SatT ty mem ψ v := by
  simp only [or, satT_neg, satT_and]; tauto

@[simp] lemma satT_imp : SatT ty mem (imp φ ψ) v ↔ (SatT ty mem φ v → SatT ty mem ψ v) := by
  simp only [imp, satT_neg, satT_and]; tauto

@[simp] lemma satT_iff : SatT ty mem (iff φ ψ) v ↔ (SatT ty mem φ v ↔ SatT ty mem ψ v) := by
  simp only [iff, satT_and, satT_imp]; tauto

@[simp] lemma satT_ex {t : ℕ} :
    SatT ty mem (ex t φ) v ↔ ∃ a, ty t a ∧ SatT ty mem φ (scons a v) := by
  simp only [ex, satT_neg, satT_all]; push_neg; rfl

end

section

variable {Γ : List ℕ} {φ ψ : TFm}

@[simp] lemma strat_neg : Strat Γ (.neg φ) ↔ Strat Γ φ := Iff.rfl

@[simp] lemma strat_and : Strat Γ (.and φ ψ) ↔ Strat Γ φ ∧ Strat Γ ψ := Iff.rfl

@[simp] lemma strat_all {t : ℕ} : Strat Γ (.all t φ) ↔ Strat (t :: Γ) φ := Iff.rfl

@[simp] lemma strat_or : Strat Γ (or φ ψ) ↔ Strat Γ φ ∧ Strat Γ ψ := Iff.rfl

@[simp] lemma strat_imp : Strat Γ (imp φ ψ) ↔ Strat Γ φ ∧ Strat Γ ψ := Iff.rfl

@[simp] lemma strat_iff : Strat Γ (iff φ ψ) ↔ Strat Γ φ ∧ Strat Γ ψ := by
  simp only [iff, strat_and, strat_imp]; tauto

@[simp] lemma strat_ex {t : ℕ} : Strat Γ (ex t φ) ↔ Strat (t :: Γ) φ := Iff.rfl

lemma strat_mem {i j t : ℕ} (hi : Γ[i]? = some t) (hj : Γ[j]? = some (t + 1)) :
    Strat Γ (.mem i j) := ⟨t, hi, hj⟩

lemma strat_eq {i j t : ℕ} (hi : Γ[i]? = some t) (hj : Γ[j]? = some t) :
    Strat Γ (.eq i j) := ⟨t, hi, hj⟩

end

/-- A well typed formula depends only on the values of its free variables. -/
lemma satT_congr {M : Type*} {ty : ℕ → M → Prop} {mem : M → M → Prop} (φ : TFm) :
    ∀ (Γ : List ℕ) (v v' : ℕ → M), Strat Γ φ → (∀ i, i < Γ.length → v i = v' i) →
      (SatT ty mem φ v ↔ SatT ty mem φ v') := by
  induction φ with
  | mem i j =>
    rintro Γ v v' ⟨t, hi, hj⟩ h
    have hi' : i < Γ.length := (List.getElem?_eq_some_iff.mp hi).1
    have hj' : j < Γ.length := (List.getElem?_eq_some_iff.mp hj).1
    simp only [satT_mem, h i hi', h j hj']
  | eq i j =>
    rintro Γ v v' ⟨t, hi, hj⟩ h
    have hi' : i < Γ.length := (List.getElem?_eq_some_iff.mp hi).1
    have hj' : j < Γ.length := (List.getElem?_eq_some_iff.mp hj).1
    simp only [satT_eq, h i hi', h j hj']
  | neg φ ih =>
    intro Γ v v' hs h
    simp only [satT_neg, ih Γ v v' hs h]
  | and φ ψ ih1 ih2 =>
    intro Γ v v' hs h
    simp only [satT_and, ih1 Γ v v' hs.1 h, ih2 Γ v v' hs.2 h]
  | all t φ ih =>
    intro Γ v v' hs h
    simp only [satT_all]
    refine forall_congr' fun a => imp_congr_right fun _ => ih (t :: Γ) _ _ hs ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by simpa using hi)

/-- **The universe of type `k` is not finite**: some family (of type `k + 2`) contains every
object of type `k + 1` without members and is closed under adjoining one element, but contains
no universal set. This is `Axiom.universeInfinite` with the types `k`, `k + 1`, `k + 2`. -/
def infFm (k : ℕ) : TFm :=
  ex (k + 2) (.and (.and
    (.all (k + 1) (imp (.all k (.neg (.mem 0 1))) (.mem 0 1)))
    (.all (k + 1) (imp (.mem 0 1) (.all k (.all (k + 1)
      (imp (.all k (iff (.mem 0 1) (or (.mem 0 3) (.eq 0 2)))) (.mem 0 3)))))))
    (.all (k + 1) (imp (.all k (.mem 0 1)) (.neg (.mem 0 1)))))

lemma strat_infFm (k : ℕ) (Γ : List ℕ) : Strat Γ (infFm k) := by
  simp [infFm, Strat]

lemma satT_infFm {M : Type*} {ty : ℕ → M → Prop} {mem : M → M → Prop} {k : ℕ} {v : ℕ → M} :
    SatT ty mem (infFm k) v ↔ ∃ F, ty (k + 2) F ∧
      (∀ e, ty (k + 1) e → (∀ z, ty k z → ¬mem z e) → mem e F) ∧
      (∀ s, ty (k + 1) s → mem s F → ∀ b, ty k b → ∀ s', ty (k + 1) s' →
        (∀ z, ty k z → (mem z s' ↔ mem z s ∨ z = b)) → mem s' F) ∧
      ∀ u, ty (k + 1) u → (∀ z, ty k z → mem z u) → ¬mem u F := by
  simp [infFm, and_assoc]


lemma bd_infFm_le (k : ℕ) : (infFm k).bd ≤ k + 3 := by
  simp only [infFm, bd, ex, imp, iff, or]
  omega

section

variable {V : Type} {mem : V → V → Prop} {φ ψ : TFm} {env : List V}

lemma sat_or : Sat mem (or φ ψ) env ↔ Sat mem φ env ∨ Sat mem ψ env := by
  simp only [or, Sat]; tauto

lemma sat_imp : Sat mem (imp φ ψ) env ↔ (Sat mem φ env → Sat mem ψ env) := by
  simp only [imp, Sat]; tauto

lemma sat_iff : Sat mem (iff φ ψ) env ↔ (Sat mem φ env ↔ Sat mem ψ env) := by
  simp only [iff, Sat, sat_imp]; tauto

lemma sat_ex {t : ℕ} : Sat mem (ex t φ) env ↔ ∃ a, Sat mem φ (a :: env) := by
  simp only [ex, Sat]; push_neg; rfl

/-- In a structure without types, `infFm k` says that the universe is not finite. -/
lemma sat_infFm {k : ℕ} : Sat mem (infFm k) [] ↔ UnivInfinite mem := by
  simp only [infFm, sat_ex, Sat, sat_imp, sat_iff, sat_or, List.getElem?_cons_zero,
    List.getElem?_cons_succ, ex_some, UnivInfinite, and_assoc]

end

end TFm

end JensenNFU
