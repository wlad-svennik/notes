import TFmExtra

set_option autoImplicit false

/-!
# Jensen's model over an arbitrary base

`NFUJensenModel.lean` builds a model of NFU with an infinite universe from the iterated power
sets of `ℕ`. The construction uses that base through three facts only. This file repeats the
construction with the base as a parameter, so that it applies to the levels of any model of
type theory.

* **The base** (`JBase C`): a carrier `C`, a level `lev x` for each object, and a relation `E`,
  such that for every strictly increasing sequence of levels `ℓ` the structure "type `t` is the
  level `ℓ t`, membership is `E`" has
  * extensionality for objects with members (`ext_base`);
  * comprehension **for typed formulas** (`comp_base`). In `NFUJensenModel.lean` every collection
    has a code; in a model of type theory only the definable ones do;
  * a universe of type 0 that is not finite (`inf_base`), stated by the typed formula
    `TFm.infFm 0`.
* **The model** `V C`: functions of finite support from generic points to `C`, of the level of
  index 0, up to equality almost everywhere. Membership compares `x` with the shift of `y`.
* **Results**: `isNFU_V`, `inf_V`, and `exists_levels`: every well typed sentence that is true in
  the model is true in the base along some strictly increasing sequence of levels.

The text from `PreE` to `ext_V` is that of `NFUJensenModel.lean` with `C` as a parameter. The
proofs of `comp_V` and `inf_V` are new. Only Mathlib is used.
-/

open Filter
open ConNF.NF (Pt genW sh sh_sh sh_zero ev_sh ev_lt FinSupp)

namespace JensenNFU

namespace Gen

/-- The data of a base: a level for each object, a membership relation, and an object. -/
class JBase₀ (C : Type) where
  lev : C → ℕ
  E : C → C → Prop
  ne : Nonempty C

section

variable {C : Type} [JBase₀ C]

/-- The level of an object. -/
abbrev lev (x : C) : ℕ := JBase₀.lev x

/-- Membership in the base. -/
abbrev E (x y : C) : Prop := JBase₀.E x y

/-- Satisfaction in the base, where a quantifier of type `t` ranges over the level `ℓ t`. -/
def TSat (ℓ : ℕ → ℕ) : TFm → List C → Prop
  | .mem i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ E a b
  | .eq i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ a = b
  | .neg φ, env => ¬TSat ℓ φ env
  | .and φ ψ, env => TSat ℓ φ env ∧ TSat ℓ ψ env
  | .all t φ, env => ∀ a, lev a = ℓ t → TSat ℓ φ (a :: env)

end

/-- **A base.** For every strictly increasing sequence of levels `ℓ`, the structure in which
the objects of type `t` are those of level `ℓ t` satisfies extensionality for objects with
members, comprehension for well typed formulas, and "the universe of type 0 is not finite". -/
class JBase (C : Type) extends JBase₀ C where
  ext_base : ∀ {a b : ℕ} {y y' : C}, lev y = b → lev y' = b → (∃ x : C, lev x = a ∧ E x y) →
    (∀ x : C, lev x = a → (E x y ↔ E x y')) → y = y'
  comp_base : ∀ (ℓ : ℕ → ℕ), StrictMono ℓ → ∀ (t : ℕ) (Γ : List ℕ) (φ : TFm),
    TFm.Strat (t :: Γ) φ → ∀ env : List C, List.Forall₂ (fun s c => lev c = ℓ s) Γ env →
      ∃ c : C, lev c = ℓ (t + 1) ∧ ∀ x : C, lev x = ℓ t → (E x c ↔ TSat ℓ φ (x :: env))
  inf_base : ∀ ℓ : ℕ → ℕ, StrictMono ℓ → TSat (C := C) ℓ (TFm.infFm 0) []

section

variable {C : Type} [JBase₀ C]

/-! ## Pre-elements -/

/-- A function of finite support from generic points to the base. -/
structure PreE (C : Type) where
  f : Pt → C
  fin : FS f

theorem PreE.ext {F G : PreE C} (h : F.f = G.f) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Shift a pre-element along the sequence of levels. -/
def PreE.shift (m : ℤ) (F : PreE C) : PreE C where
  f p := F.f (sh m p.1, p.2)
  fin := by
    obtain ⟨N, hN⟩ := F.fin
    exact ⟨N + m.natAbs, fun v v' D h => hN _ _ D fun k hk1 hk2 => h (k + m) (by omega) (by omega)⟩

@[simp] theorem PreE.shift_shift (F : PreE C) (a b : ℤ) :
    (F.shift a).shift b = F.shift (a + b) := by
  apply PreE.ext
  funext p
  show F.f (sh a (sh b p.1), p.2) = F.f (sh (a + b) p.1, p.2)
  rw [sh_sh]

@[simp] theorem PreE.shift_zero (F : PreE C) : F.shift 0 = F := by
  apply PreE.ext
  funext p
  show F.f (sh 0 p.1, p.2) = F.f p
  rw [sh_zero]

/-- Membership almost everywhere. -/
def EE (F G : PreE C) : Prop := ∀ᶠ p in (genW : Filter Pt), E (F.f p) (G.f p)

/-- Equality almost everywhere. -/
def Eqv (F G : PreE C) : Prop := ∀ᶠ p in (genW : Filter Pt), F.f p = G.f p

/-- Almost everywhere, `F` has the level of index `k`. -/
def IsLev (k : ℤ) (F : PreE C) : Prop := ∀ᶠ p in (genW : Filter Pt), lev (F.f p) = p.1 k

theorem EE_shift (m : ℤ) (F G : PreE C) : EE (F.shift m) (G.shift m) ↔ EE F G :=
  ev_shift (P := fun p => E (F.f p) (G.f p)) (FS.map₂ F.fin G.fin E) m

theorem Eqv_shift (m : ℤ) (F G : PreE C) : Eqv (F.shift m) (G.shift m) ↔ Eqv F G :=
  ev_shift (P := fun p => F.f p = G.f p) (FS.map₂ F.fin G.fin fun x y => x = y) m

theorem IsLev_shift (k m : ℤ) (F : PreE C) : IsLev (k + m) (F.shift m) ↔ IsLev k F :=
  ev_shift (P := fun p => lev (F.f p) = p.1 k)
    (FS.map₂ F.fin (FS.coord k) fun x n => lev x = n) m

theorem IsLev.shift' {F : PreE C} (h : IsLev 0 F) (m : ℤ) : IsLev m (F.shift m) := by
  have := (IsLev_shift 0 m F).mpr h
  rwa [zero_add] at this

theorem Eqv.refl (F : PreE C) : Eqv F F := Eventually.of_forall fun _ => rfl

theorem Eqv.symm {F G : PreE C} (h : Eqv F G) : Eqv G F := h.mono fun _ hp => hp.symm

theorem Eqv.trans {F G H : PreE C} (h₁ : Eqv F G) (h₂ : Eqv G H) : Eqv F H := by
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  exact hp₁.trans hp₂

/-- **Witnesses.** A family of predicates of finite support has a pre-element that satisfies the
predicate wherever something does. -/
theorem exists_wit (R : Pt → C → Prop) (hR : FS R) :
    ∃ w : PreE C, ∀ p, (∃ a, R p a) → R p (w.f p) := by
  haveI : Nonempty C := JBase₀.ne
  refine ⟨⟨fun p => Classical.epsilon (R p), ?_⟩, fun p h => Classical.epsilon_spec h⟩
  obtain ⟨N, hN⟩ := hR
  refine ⟨N, fun v v' D h => ?_⟩
  show Classical.epsilon (R (v, D)) = Classical.epsilon (R (v', D))
  rw [hN v v' D h]

/-! ## The structure -/

/-- Pre-elements of the level of index 0. -/
def V₀ (C : Type) [JBase₀ C] : Type := {F : PreE C // IsLev 0 F}

instance V₀.setoid : Setoid (V₀ C) where
  r x y := Eqv x.1 y.1
  iseqv := ⟨fun x => Eqv.refl x.1, Eqv.symm, Eqv.trans⟩

/-- **The universe of the model.** -/
def V (C : Type) [JBase₀ C] : Type := Quotient (V₀.setoid (C := C))

/-- `x ∈ y`: almost everywhere, `x` is a member of the shift of `y`. -/
def mem₀ (x y : V₀ C) : Prop := EE x.1 (y.1.shift 1)

theorem mem₀_iff (x y : V₀ C) (m : ℤ) : mem₀ x y ↔ EE (x.1.shift m) (y.1.shift (1 + m)) := by
  rw [← PreE.shift_shift]
  exact (EE_shift m _ _).symm

theorem mem₀_congr {x x' y y' : V₀ C} (hx : Eqv x.1 x'.1) (hy : Eqv y.1 y'.1) :
    mem₀ x y ↔ mem₀ x' y' := by
  have hy1 : Eqv (y.1.shift 1) (y'.1.shift 1) := (Eqv_shift 1 _ _).mpr hy
  constructor
  · intro h
    filter_upwards [h, hx, hy1] with p h1 h2 h3
    rw [← h2, ← h3]
    exact h1
  · intro h
    filter_upwards [h, hx, hy1] with p h1 h2 h3
    rw [h2, h3]
    exact h1

/-- **The membership relation of the model.** -/
def memV : V C → V C → Prop :=
  Quotient.lift₂ mem₀ fun _ _ _ _ hx hy => propext (mem₀_congr hx hy)

/-- The class of a pre-element. -/
def mk (x : V₀ C) : V C := Quotient.mk V₀.setoid x

theorem memV_mk (x y : V₀ C) : memV (mk x) (mk y) ↔ mem₀ x y := Iff.rfl

theorem mk_eq_iff {x y : V₀ C} : mk x = mk y ↔ Eqv x.1 y.1 := Quotient.eq

theorem mk_surj (a : V C) : ∃ x, mk x = a := Quotient.exists_rep a

/-- Bring a pre-element of the level of index `k` down to index 0. -/
def lower (k : ℤ) (F : PreE C) (h : IsLev k F) : V₀ C :=
  ⟨F.shift (-k), by
    have := (IsLev_shift k (-k) F).mpr h
    rwa [add_neg_cancel] at this⟩

theorem lower_shift (k : ℤ) (F : PreE C) (h : IsLev k F) : (lower k F h).1.shift k = F := by
  show (F.shift (-k)).shift k = F
  rw [PreE.shift_shift, neg_add_cancel, PreE.shift_zero]


/-! ## Łoś's theorem -/

theorem TSat_congr {ℓ ℓ' : ℕ → ℕ} (φ : TFm) (h : ∀ t, t < φ.bd → ℓ t = ℓ' t) :
    TSat (C := C) ℓ φ = TSat ℓ' φ := by
  induction φ with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih =>
    funext env
    simp only [TSat]
    rw [ih h]
  | and φ ψ ih1 ih2 =>
    funext env
    simp only [TSat]
    rw [ih1 fun t ht => h t (lt_of_lt_of_le ht (le_max_left _ _)),
      ih2 fun t ht => h t (lt_of_lt_of_le ht (le_max_right _ _))]
  | all t φ ih =>
    funext env
    simp only [TSat]
    rw [ih fun s hs => h s (lt_of_lt_of_le hs (le_max_right _ _)),
      h t (lt_of_lt_of_le (Nat.lt_succ_self t) (le_max_left _ _))]

/-- The levels at a generic point. -/
def lvOf (p : Pt) : ℕ → ℕ := fun t => p.1 (t : ℤ)

theorem FS_tsat (φ : TFm) : FS (fun p : Pt => TSat (C := C) (lvOf p) φ) :=
  ⟨φ.bd, fun _ _ _ h => TSat_congr φ fun t ht => h t (by omega) (by omega)⟩

/-- The values at a generic point of a list of typed pre-elements: the one of type `t` is
shifted to the level of index `t`. -/
def pt (ys : List (ℕ × V₀ C)) (p : Pt) : List C := ys.map fun y => (y.2.1.shift y.1).f p

theorem FS_pt : ∀ ys : List (ℕ × V₀ C), FS (pt ys)
  | [] => ⟨0, fun _ _ _ _ => rfl⟩
  | y :: ys => FS.map₂ (y.2.1.shift y.1).fin (FS_pt ys) fun a l => a :: l

theorem ex_some {α : Type*} {u w : α} {R : α → α → Prop} :
    (∃ a b, some u = some a ∧ some w = some b ∧ R a b) ↔ R u w :=
  ⟨fun ⟨a, b, ha, hb, h⟩ => by cases ha; cases hb; exact h, fun h => ⟨u, w, rfl, rfl, h⟩⟩

/-- **Łoś's theorem** for stratified formulas. -/
theorem los (φ : TFm) : ∀ ys : List (ℕ × V₀ C), TFm.Strat (ys.map Prod.fst) φ →
    (TFm.Sat memV φ (ys.map fun y => mk y.2) ↔
      ∀ᶠ p in (genW : Filter Pt), TSat (lvOf p) φ (pt ys p)) := by
  induction φ with
  | mem i j =>
    rintro ys ⟨t, hi, hj⟩
    rw [List.getElem?_map] at hi hj
    obtain ⟨⟨t1, x⟩, hxi, ht1⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨⟨t2, y⟩, hyj, ht2⟩ := Option.map_eq_some_iff.mp hj
    simp only at ht1 ht2
    subst ht1
    subst ht2
    have e1 : (ys.map fun y => mk y.2)[i]? = some (mk x) := by
      rw [List.getElem?_map, hxi]; rfl
    have e2 : (ys.map fun y => mk y.2)[j]? = some (mk y) := by
      rw [List.getElem?_map, hyj]; rfl
    have e3 : ∀ p, (pt ys p)[i]? = some ((x.1.shift (t1 : ℤ)).f p) := fun p => by
      rw [pt, List.getElem?_map, hxi]; rfl
    have e4 : ∀ p, (pt ys p)[j]? = some ((y.1.shift ((t1 + 1 : ℕ) : ℤ)).f p) := fun p => by
      rw [pt, List.getElem?_map, hyj]; rfl
    simp only [TFm.Sat, TSat, e1, e2, e3, e4, ex_some]
    have key := mem₀_iff x y (t1 : ℤ)
    rw [show (1 : ℤ) + (t1 : ℤ) = ((t1 + 1 : ℕ) : ℤ) by push_cast; ring] at key
    exact key
  | eq i j =>
    rintro ys ⟨t, hi, hj⟩
    rw [List.getElem?_map] at hi hj
    obtain ⟨⟨t1, x⟩, hxi, ht1⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨⟨t2, y⟩, hyj, ht2⟩ := Option.map_eq_some_iff.mp hj
    simp only at ht1 ht2
    subst ht1
    subst ht2
    have e1 : (ys.map fun y => mk y.2)[i]? = some (mk x) := by
      rw [List.getElem?_map, hxi]; rfl
    have e2 : (ys.map fun y => mk y.2)[j]? = some (mk y) := by
      rw [List.getElem?_map, hyj]; rfl
    have e3 : ∀ p, (pt ys p)[i]? = some ((x.1.shift (t2 : ℤ)).f p) := fun p => by
      rw [pt, List.getElem?_map, hxi]; rfl
    have e4 : ∀ p, (pt ys p)[j]? = some ((y.1.shift (t2 : ℤ)).f p) := fun p => by
      rw [pt, List.getElem?_map, hyj]; rfl
    simp only [TFm.Sat, TSat, e1, e2, e3, e4, ex_some]
    exact mk_eq_iff.trans (Eqv_shift (t2 : ℤ) x.1 y.1).symm
  | neg φ ih =>
    intro ys hs
    simp only [TFm.Sat, TSat]
    rw [ih ys hs]
    exact Ultrafilter.eventually_not.symm
  | and φ ψ ih1 ih2 =>
    intro ys hs
    simp only [TFm.Sat, TSat]
    rw [ih1 ys hs.1, ih2 ys hs.2]
    exact eventually_and.symm
  | all t φ ih =>
    intro ys hs
    have hs' : ∀ x : V₀ C, TFm.Strat (((t, x) :: ys).map Prod.fst) φ := fun _ => hs
    simp only [TFm.Sat, TSat]
    constructor
    · intro h
      by_contra hcon
      rw [← Ultrafilter.eventually_not] at hcon
      have hR : FS (fun (p : Pt) (a : C) => lev a = lvOf p t ∧ ¬TSat (lvOf p) φ (a :: pt ys p)) :=
        FS.map₃ (FS.coord (t : ℤ)) (FS_tsat φ) (FS_pt ys)
          (fun n T l => fun a => lev a = n ∧ ¬T (a :: l))
      obtain ⟨w, hw⟩ := exists_wit _ hR
      have hw' : ∀ᶠ p in (genW : Filter Pt),
          lev (w.f p) = lvOf p t ∧ ¬TSat (lvOf p) φ (w.f p :: pt ys p) := by
        filter_upwards [hcon] with p hp
        apply hw p
        by_contra hne
        exact hp fun a ha => by_contra fun hT => hne ⟨a, ha, hT⟩
      have hlev : IsLev (t : ℤ) w := hw'.mono fun p hp => hp.1
      have key := (ih ((t, lower t w hlev) :: ys) (hs' _)).mp (h (mk (lower t w hlev)))
      have e : ∀ p, pt ((t, lower t w hlev) :: ys) p = w.f p :: pt ys p := fun p => by
        show ((lower t w hlev).1.shift t).f p :: pt ys p = w.f p :: pt ys p
        rw [lower_shift]
      simp only [e] at key
      obtain ⟨p, hp1, hp2⟩ := (key.and hw').exists
      exact hp2.2 hp1
    · intro h a
      obtain ⟨x, rfl⟩ := mk_surj a
      refine (ih ((t, x) :: ys) (hs' x)).mpr ?_
      filter_upwards [h, x.2.shift' (t : ℤ)] with p hp hl
      exact hp _ hl

/-! ## The axioms -/

theorem exists_reps : ∀ (Γ : List ℕ) (params : List (V C)), params.length = Γ.length →
    ∃ ys : List (ℕ × V₀ C), ys.map Prod.fst = Γ ∧ (ys.map fun y => mk y.2) = params
  | [], [], _ => ⟨[], rfl, rfl⟩
  | t :: Γ, a :: params, h => by
    obtain ⟨ys, h1, h2⟩ := exists_reps Γ params (by simpa using h)
    obtain ⟨x, rfl⟩ := mk_surj a
    exact ⟨(t, x) :: ys, by simp [h1], by simp [h2]⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h


/-- Satisfaction with a list as environment agrees with satisfaction with a function as
environment (`TFm.SatT`), for well typed formulas. -/
theorem tsat_iff_satT (d : C) (ℓ : ℕ → ℕ) (φ : TFm) :
    ∀ (Γ : List ℕ) (env : List C), TFm.Strat Γ φ → env.length = Γ.length →
      (TSat ℓ φ env ↔ TFm.SatT (fun t c => lev c = ℓ t) E φ (fun i => env.getD i d)) := by
  induction φ with
  | mem i j =>
    rintro Γ env ⟨t, hi, hj⟩ hlen
    have hi' : i < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hj' : j < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
    simp only [TSat, TFm.satT_mem]
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
      List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
    exact ex_some
  | eq i j =>
    rintro Γ env ⟨t, hi, hj⟩ hlen
    have hi' : i < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    have hj' : j < env.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
    simp only [TSat, TFm.satT_eq]
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
      List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
    exact ex_some
  | neg φ ih =>
    intro Γ env hs hlen
    simp only [TSat, TFm.satT_neg, ih Γ env hs hlen]
  | and φ ψ ih1 ih2 =>
    intro Γ env hs hlen
    simp only [TSat, TFm.satT_and, ih1 Γ env hs.1 hlen, ih2 Γ env hs.2 hlen]
  | all t φ ih =>
    intro Γ env hs hlen
    simp only [TSat, TFm.satT_all]
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    rw [ih (t :: Γ) (a :: env) hs (by simp [hlen])]
    have : (fun i => (a :: env).getD i d) = TFm.scons a (fun i => env.getD i d) := by
      funext i
      cases i <;> simp
    rw [this]

/-! ## Strictly increasing sequences of levels -/

/-- Extend a function that increases up to `K` to a strictly increasing one. -/
def monoExt (f : ℕ → ℕ) (K : ℕ) : ℕ → ℕ := fun i => if i ≤ K then f i else f K + (i - K)

theorem monoExt_of_le {f : ℕ → ℕ} {K i : ℕ} (h : i ≤ K) : monoExt f K i = f i := if_pos h

theorem monoExt_strictMono {f : ℕ → ℕ} {K : ℕ} (h : ∀ i, i < K → f i < f (i + 1)) :
    StrictMono (monoExt f K) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  unfold monoExt
  by_cases h1 : n + 1 ≤ K
  · rw [if_pos (by omega), if_pos h1]
    exact h n (by omega)
  · by_cases h2 : n ≤ K
    · have : n = K := by omega
      subst this
      rw [if_pos le_rfl, if_neg (by omega)]
      omega
    · rw [if_neg h2, if_neg (by omega)]
      omega

/-- Almost everywhere, the levels of the indices `0, …, K` are increasing. -/
theorem ev_incr (K : ℕ) :
    ∀ᶠ p in (genW : Filter Pt), ∀ i, i < K → lvOf p i < lvOf p (i + 1) := by
  induction K with
  | zero => exact Eventually.of_forall fun _ i hi => absurd hi (Nat.not_lt_zero i)
  | succ K ih =>
    have h : ∀ᶠ p in (genW : Filter Pt), p.1 (K : ℤ) < p.1 ((K + 1 : ℕ) : ℤ) :=
      ev_lt (by push_cast; omega)
    filter_upwards [ih, h] with p h1 h2 i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h3 | rfl
    · exact h1 i h3
    · exact h2

/-- A bound on a list of types. -/
def tyBound : List ℕ → ℕ
  | [] => 0
  | s :: Γ => max s (tyBound Γ)

/-- Almost everywhere, the values of typed pre-elements have the levels of their types. -/
theorem ev_pt_lev : ∀ (ys : List (ℕ × V₀ C)) (K : ℕ), tyBound (ys.map Prod.fst) ≤ K →
    ∀ᶠ p in (genW : Filter Pt),
      List.Forall₂ (fun s c => lev c = monoExt (lvOf p) K s) (ys.map Prod.fst) (pt ys p)
  | [], _, _ => Eventually.of_forall fun _ => List.Forall₂.nil
  | y :: ys, K, h => by
    have h1 : y.1 ≤ K := le_trans (le_max_left _ _) h
    have h2 : tyBound (ys.map Prod.fst) ≤ K := le_trans (le_max_right _ _) h
    have hy : IsLev (y.1 : ℤ) (y.2.1.shift y.1) := y.2.2.shift' y.1
    filter_upwards [ev_pt_lev ys K h2, hy] with p hp1 hp2
    exact List.Forall₂.cons (by rw [monoExt_of_le h1]; exact hp2) hp1

end

section

variable {C : Type} [JBase C]

/-- **Stratified comprehension.** -/
theorem comp_V (t : ℕ) (Γ : List ℕ) (φ : TFm) (hs : TFm.Strat (t :: Γ) φ) (params : List (V C))
    (hp : params.length = Γ.length) :
    ∃ y : V C, ∀ x : V C, memV x y ↔ TFm.Sat memV φ (x :: params) := by
  obtain ⟨ys, rfl, rfl⟩ := exists_reps Γ params hp
  have hR : FS (fun (p : Pt) (c : C) => lev c = p.1 ((t + 1 : ℕ) : ℤ) ∧
      ∀ a, lev a = p.1 (t : ℤ) → (E a c ↔ TSat (lvOf p) φ (a :: pt ys p))) :=
    FS.map₄ (FS.coord ((t + 1 : ℕ) : ℤ)) (FS.coord (t : ℤ)) (FS_tsat φ) (FS_pt ys)
      (fun n1 n0 T l => fun c => lev c = n1 ∧ ∀ a, lev a = n0 → (E a c ↔ T (a :: l)))
  obtain ⟨w, hw⟩ := exists_wit _ hR
  have hK1 : tyBound (ys.map Prod.fst) ≤ max φ.bd (max (t + 1) (tyBound (ys.map Prod.fst))) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hK2 : t + 1 ≤ max φ.bd (max (t + 1) (tyBound (ys.map Prod.fst))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hK3 : φ.bd ≤ max φ.bd (max (t + 1) (tyBound (ys.map Prod.fst))) := le_max_left _ _
  have hw' : ∀ᶠ p in (genW : Filter Pt), lev (w.f p) = p.1 ((t + 1 : ℕ) : ℤ) ∧
      ∀ a, lev a = p.1 (t : ℤ) → (E a (w.f p) ↔ TSat (lvOf p) φ (a :: pt ys p)) := by
    filter_upwards [ev_incr (max φ.bd (max (t + 1) (tyBound (ys.map Prod.fst)))),
      ev_pt_lev ys _ hK1] with p hp1 hp2
    apply hw p
    obtain ⟨c, hc1, hc2⟩ := JBase.comp_base _ (monoExt_strictMono hp1) t (ys.map Prod.fst) φ hs
      (pt ys p) hp2
    have e1 : monoExt (lvOf p) (max φ.bd (max (t + 1) (tyBound (ys.map Prod.fst)))) (t + 1) =
        p.1 ((t + 1 : ℕ) : ℤ) := monoExt_of_le hK2
    have e0 : monoExt (lvOf p) (max φ.bd (max (t + 1) (tyBound (ys.map Prod.fst)))) t =
        p.1 (t : ℤ) := monoExt_of_le (le_trans (Nat.le_succ t) hK2)
    have e2 : TSat (C := C) (monoExt (lvOf p) (max φ.bd (max (t + 1) (tyBound (ys.map Prod.fst)))))
        φ = TSat (lvOf p) φ :=
      TSat_congr φ fun s hs' => monoExt_of_le (le_trans (le_of_lt hs') hK3)
    exact ⟨c, by rw [← e1]; exact hc1, fun a ha => by
      rw [← e2]; exact hc2 a (by rw [e0]; exact ha)⟩
  have hlev : IsLev ((t + 1 : ℕ) : ℤ) w := hw'.mono fun p hp => hp.1
  refine ⟨mk (lower _ w hlev), fun x => ?_⟩
  obtain ⟨x, rfl⟩ := mk_surj x
  rw [memV_mk, mem₀_iff x _ (t : ℤ)]
  have e1 : (lower ((t + 1 : ℕ) : ℤ) w hlev).1.shift (1 + (t : ℤ)) = w := by
    rw [show (1 : ℤ) + (t : ℤ) = ((t + 1 : ℕ) : ℤ) by push_cast; ring]
    exact lower_shift _ _ _
  rw [e1]
  have hlos := los φ ((t, x) :: ys) hs
  have hx : IsLev (t : ℤ) (x.1.shift t) := x.2.shift' t
  refine Iff.trans ?_ hlos.symm
  constructor
  · intro h
    filter_upwards [h, hw', hx] with p h1 h2 h3
    exact (h2.2 _ h3).mp h1
  · intro h
    filter_upwards [h, hw', hx] with p h1 h2 h3
    exact (h2.2 _ h3).mpr h1

/-- **Extensionality for objects with members.** -/
theorem ext_V (x y : V C) (hne : ∃ z, memV z x) (h : ∀ z, memV z x ↔ memV z y) : x = y := by
  obtain ⟨x, rfl⟩ := mk_surj x
  obtain ⟨y, rfl⟩ := mk_surj y
  obtain ⟨z, hz⟩ := hne
  obtain ⟨z, rfl⟩ := mk_surj z
  rw [mk_eq_iff, ← Eqv_shift 1]
  by_contra hcon
  have hcon' : ∀ᶠ p in (genW : Filter Pt), ¬(x.1.shift 1).f p = (y.1.shift 1).f p :=
    Ultrafilter.eventually_not.mpr hcon
  have hx : IsLev 1 (x.1.shift 1) := x.2.shift' 1
  have hy : IsLev 1 (y.1.shift 1) := y.2.shift' 1
  have hz' : ∀ᶠ p in (genW : Filter Pt), E (z.1.f p) ((x.1.shift 1).f p) := hz
  have hR : FS (fun (p : Pt) (a : C) => lev a = p.1 0 ∧
      ¬(E a ((x.1.shift 1).f p) ↔ E a ((y.1.shift 1).f p))) :=
    FS.map₃ (FS.coord 0) (x.1.shift 1).fin (y.1.shift 1).fin
      (fun n X Y => fun a => lev a = n ∧ ¬(E a X ↔ E a Y))
  obtain ⟨w, hw⟩ := exists_wit _ hR
  have hw' : ∀ᶠ p in (genW : Filter Pt), lev (w.f p) = p.1 0 ∧
      ¬(E (w.f p) ((x.1.shift 1).f p) ↔ E (w.f p) ((y.1.shift 1).f p)) := by
    filter_upwards [hcon', hx, hy, hz', z.2] with p h1 h2 h3 h4 h5
    apply hw p
    by_contra hno
    apply h1
    exact JBase.ext_base h2 h3 ⟨z.1.f p, h5, h4⟩ fun a ha => by_contra fun hiff => hno ⟨a, ha, hiff⟩
  have hlev : IsLev 0 w := hw'.mono fun p hp => hp.1
  have key : EE w (x.1.shift 1) ↔ EE w (y.1.shift 1) := h (mk ⟨w, hlev⟩)
  by_cases hX : EE w (x.1.shift 1)
  · have hY : EE w (y.1.shift 1) := key.mp hX
    obtain ⟨p, hp1, hp2, hp3⟩ := (hw'.and (hX.and hY)).exists
    exact hp1.2 ⟨fun _ => hp3, fun _ => hp2⟩
  · have hY : ¬EE w (y.1.shift 1) := fun hY => hX (key.mpr hY)
    have hX' : ∀ᶠ p in (genW : Filter Pt), ¬E (w.f p) ((x.1.shift 1).f p) :=
      Ultrafilter.eventually_not.mpr hX
    have hY' : ∀ᶠ p in (genW : Filter Pt), ¬E (w.f p) ((y.1.shift 1).f p) :=
      Ultrafilter.eventually_not.mpr hY
    obtain ⟨p, hp1, hp2, hp3⟩ := (hw'.and (hX'.and hY')).exists
    exact hp1.2 ⟨fun h => absurd h hp2, fun h => absurd h hp3⟩


/-- **The universe is not finite.** -/
theorem inf_V : UnivInfinite (memV (C := C)) := by
  have hlos := los (C := C) (TFm.infFm 0) [] (TFm.strat_infFm 0 _)
  have h : ∀ᶠ p in (genW : Filter Pt), TSat (C := C) (lvOf p) (TFm.infFm 0) [] := by
    filter_upwards [ev_incr 3] with p hp
    have := JBase.inf_base (C := C) (monoExt (lvOf p) 3) (monoExt_strictMono hp)
    rwa [TSat_congr (C := C) (ℓ := monoExt (lvOf p) 3) (ℓ' := lvOf p) (TFm.infFm 0)
      (fun s hs => monoExt_of_le (by have := TFm.bd_infFm_le 0; omega))] at this
  exact TFm.sat_infFm.mp (hlos.mpr h)

/-- **The structure is a model of NFU.** -/
theorem isNFU_V : IsNFU (V C) memV := ⟨ext_V, comp_V⟩

/-- **The model reflects the base.** A well typed sentence that is true in the model is true in
the base along some strictly increasing sequence of levels. -/
theorem exists_levels (φ : TFm) (h : TFm.Strat [] φ) (hφ : TFm.Sat (memV (C := C)) φ []) :
    ∃ ℓ : ℕ → ℕ, StrictMono ℓ ∧ TSat (C := C) ℓ φ [] := by
  have h1 : ∀ᶠ p in (genW : Filter Pt), TSat (C := C) (lvOf p) φ [] := (los φ [] h).mp hφ
  obtain ⟨p, hp1, hp2⟩ := (h1.and (ev_incr φ.bd)).exists
  refine ⟨monoExt (lvOf p) φ.bd, monoExt_strictMono hp2, ?_⟩
  rw [TSat_congr (C := C) φ (fun s hs => monoExt_of_le (le_of_lt hs))]
  exact hp1

end

end Gen

end JensenNFU
