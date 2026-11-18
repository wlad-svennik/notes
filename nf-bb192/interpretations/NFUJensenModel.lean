import Mathlib
import ConNF.NF.Generic

set_option autoImplicit false

/-!
# A model of NFU + Infinity, after Jensen

This file constructs a structure `(V, mem)` that satisfies extensionality for objects with
members, stratified comprehension, and "the universe is not finite". It uses Mathlib and the file
`ConNF.NF.Generic`, which is itself pure Mathlib. It does not use NF or the model of tangled type
theory.

* **The base.** `Lvl 0 = ℕ` and `Lvl (n + 1) = Set (Lvl n)`. The carrier `C` is the disjoint union
  of the levels. For `a < b` every set of objects of level `a` has a code in level `b`
  (`comp_base`), and an object of level `b` that is not such a code is an urelement relative to
  level `a`.
* **The generic power.** A pre-element is a function from generic points to `C` that depends on
  only finitely many coordinates. `genW` is an ultrafilter on generic points that is invariant
  under shifting the sequence of levels (`ConNF.NF.ev_sh`) and for which the levels are
  increasing (`ConNF.NF.ev_lt`).
* **The model.** `V` consists of the pre-elements of the level of index 0, up to equality almost
  everywhere, and `x ∈ y` means that almost everywhere `x` is a member of the shift of `y`, which
  has the level of index 1.
* **Łoś's theorem** (`los`): a stratified formula holds in `V` iff almost everywhere it holds in
  the base, with a variable of type `t` shifted to the level of index `t`.
-/

open Filter
open ConNF.NF (Pt genW sh sh_sh sh_zero ev_sh ev_lt FinSupp)

namespace JensenNFU

/-! ## Formulas with typed quantifiers -/

/-- Formulas with de Bruijn indices; the quantifier carries the type of its variable. -/
inductive TFm : Type
  | mem (i j : ℕ) : TFm
  | eq (i j : ℕ) : TFm
  | neg (φ : TFm) : TFm
  | and (φ ψ : TFm) : TFm
  | all (t : ℕ) (φ : TFm) : TFm

namespace TFm

/-- Satisfaction in a structure `(V, mem)`. The types at the quantifiers play no role. -/
def Sat {V : Type} (mem : V → V → Prop) : TFm → List V → Prop
  | .mem i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ mem a b
  | .eq i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ a = b
  | .neg φ, env => ¬Sat mem φ env
  | .and φ ψ, env => Sat mem φ env ∧ Sat mem ψ env
  | .all _ φ, env => ∀ a, Sat mem φ (a :: env)

/-- `Strat Γ φ`: the formula is stratified, where `Γ` lists the types of its free variables. -/
def Strat : List ℕ → TFm → Prop
  | Γ, .mem i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some (t + 1)
  | Γ, .eq i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some t
  | Γ, .neg φ => Strat Γ φ
  | Γ, .and φ ψ => Strat Γ φ ∧ Strat Γ ψ
  | Γ, .all t φ => Strat (t :: Γ) φ

/-- A strict bound on the types at the quantifiers. -/
def bd : TFm → ℕ
  | .mem _ _ => 0
  | .eq _ _ => 0
  | .neg φ => bd φ
  | .and φ ψ => max (bd φ) (bd ψ)
  | .all t φ => max (t + 1) (bd φ)

end TFm

/-- **NFU**, as a property of a structure: extensionality for objects with members, and
comprehension for stratified formulas. -/
structure IsNFU (V : Type) (mem : V → V → Prop) : Prop where
  ext : ∀ x y, (∃ z, mem z x) → (∀ z, mem z x ↔ mem z y) → x = y
  comprehension : ∀ (t : ℕ) (Γ : List ℕ) (φ : TFm), TFm.Strat (t :: Γ) φ →
    ∀ params : List V, params.length = Γ.length → ∃ y, ∀ x, mem x y ↔ TFm.Sat mem φ (x :: params)

/-- **The universe is not finite**: some family contains every object without members and is
closed under adjoining one element, but contains no universal set. -/
def UnivInfinite {V : Type} (mem : V → V → Prop) : Prop :=
  ∃ F : V, (∀ e, (∀ z, ¬mem z e) → mem e F) ∧
    (∀ a, mem a F → ∀ b a', (∀ z, mem z a' ↔ mem z a ∨ z = b) → mem a' F) ∧
    ∀ u, (∀ z, mem z u) → ¬mem u F

/-! ## The base: iterated power sets of `ℕ`, with urelements -/

/-- The levels. -/
def Lvl : ℕ → Type
  | 0 => ℕ
  | n + 1 => Set (Lvl n)

instance instInfiniteLvl : ∀ n, Infinite (Lvl n)
  | 0 => inferInstanceAs (Infinite ℕ)
  | n + 1 => by
    have := instInfiniteLvl n
    show Infinite (Set (Lvl n))
    exact Infinite.of_injective (fun x : Lvl n => ({x} : Set (Lvl n))) Set.singleton_injective

theorem exists_emb (m : ℕ) : ∀ n, m ≤ n → Nonempty (Lvl m ↪ Lvl n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨Function.Embedding.refl _⟩
  | succ n _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨e.trans ⟨fun x : Lvl n => ({x} : Set (Lvl n)), Set.singleton_injective⟩⟩

/-- A code in level `b` for each set of objects of level `a < b`. -/
noncomputable def code (a b : ℕ) (h : a < b) : Set (Lvl a) ↪ Lvl b :=
  Classical.choice (exists_emb (a + 1) b h)

/-- The carrier: the disjoint union of the levels. -/
abbrev C : Type := Σ n, Lvl n

/-- The level of an object. -/
def lev (x : C) : ℕ := x.1

/-- Membership: `y` is the code, in its level, of a set of objects of the level of `x`, and `x`
is in that set. -/
def E (x y : C) : Prop :=
  ∃ (h : x.1 < y.1) (S : Set (Lvl x.1)), y.2 = code x.1 y.1 h S ∧ x.2 ∈ S

instance : Nonempty C := ⟨⟨0, (0 : ℕ)⟩⟩

theorem E_mk_code {a b : ℕ} (h : a < b) (S : Set (Lvl a)) (s : Lvl a) :
    E ⟨a, s⟩ ⟨b, code a b h S⟩ ↔ s ∈ S := by
  constructor
  · rintro ⟨h', S', hS', hs⟩
    have e : S = S' := (code a b h).injective hS'
    rw [e]
    exact hs
  · intro hs
    exact ⟨h, S, rfl, hs⟩

/-- Comprehension in the base: every collection of objects of level `a` has a code in each
higher level. -/
theorem comp_base {a b : ℕ} (h : a < b) (S : C → Prop) :
    ∃ c : C, lev c = b ∧ ∀ x, lev x = a → (E x c ↔ S x) := by
  refine ⟨⟨b, code a b h {s | S ⟨a, s⟩}⟩, rfl, ?_⟩
  rintro ⟨a', s⟩ hx
  simp only [lev] at hx
  subst hx
  exact E_mk_code h _ s

/-- Extensionality in the base, for objects with members. -/
theorem ext_base {a b : ℕ} {y y' : C} (hy : lev y = b) (hy' : lev y' = b)
    (hne : ∃ x, lev x = a ∧ E x y) (hmem : ∀ x, lev x = a → (E x y ↔ E x y')) : y = y' := by
  obtain ⟨b1, t⟩ := y
  obtain ⟨b2, t'⟩ := y'
  simp only [lev] at hy hy'
  subst hy
  subst hy'
  obtain ⟨⟨a1, s⟩, hx, hE⟩ := hne
  simp only [lev] at hx
  subst hx
  obtain ⟨h, S, hS, hs⟩ := hE
  obtain ⟨h', S', hS', -⟩ := (hmem ⟨a1, s⟩ rfl).mp ⟨h, S, hS, hs⟩
  have h0 : a1 < b2 := h
  have hS0 : t = code a1 b2 h0 S := hS
  have hS0' : t' = code a1 b2 h0 S' := hS'
  clear hS hS' hs h h'
  subst hS0
  subst hS0'
  have e : S = S' := by
    ext s₁
    exact (E_mk_code h0 S s₁).symm.trans ((hmem ⟨a1, s₁⟩ rfl).trans (E_mk_code h0 S' s₁))
  rw [e]

/-- Every level is infinite. -/
theorem inf_base (a : ℕ) : {x : C | lev x = a}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun s : Lvl a => (⟨a, s⟩ : C))
    (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2) (fun _ => rfl)

/-! ## Functions of finite support on generic points -/

/-- Two sequences agree on the window `[-N, N)`. -/
def Agree (N : ℕ) (v v' : ℤ → ℕ) : Prop := ∀ k : ℤ, -(N : ℤ) ≤ k → k < N → v k = v' k

/-- `g` depends on only finitely many coordinates of the sequence of levels. -/
def FS {α : Type*} (g : Pt → α) : Prop :=
  ∃ N : ℕ, ∀ (v v' : ℤ → ℕ) (D : ℕ), Agree N v v' → g (v, D) = g (v', D)

theorem FS.coord (k : ℤ) : FS (fun p : Pt => p.1 k) :=
  ⟨k.natAbs + 1, fun _ _ _ h => h k (by omega) (by omega)⟩

theorem FS.map₂ {α β γ : Type*} {g₁ : Pt → α} {g₂ : Pt → β} (h₁ : FS g₁) (h₂ : FS g₂)
    (Φ : α → β → γ) : FS (fun p => Φ (g₁ p) (g₂ p)) := by
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  refine ⟨max N₁ N₂, fun v v' D h => ?_⟩
  show Φ (g₁ (v, D)) (g₂ (v, D)) = Φ (g₁ (v', D)) (g₂ (v', D))
  rw [hN₁ v v' D fun k h1 h2 => h k (by omega) (by omega),
    hN₂ v v' D fun k h1 h2 => h k (by omega) (by omega)]

theorem FS.map₃ {α β γ δ : Type*} {g₁ : Pt → α} {g₂ : Pt → β} {g₃ : Pt → γ} (h₁ : FS g₁)
    (h₂ : FS g₂) (h₃ : FS g₃) (Φ : α → β → γ → δ) : FS (fun p => Φ (g₁ p) (g₂ p) (g₃ p)) :=
  FS.map₂ (FS.map₂ h₁ h₂ Prod.mk) h₃ (fun x z => Φ x.1 x.2 z)

theorem FS.map₄ {α β γ δ ε : Type*} {g₁ : Pt → α} {g₂ : Pt → β} {g₃ : Pt → γ} {g₄ : Pt → δ}
    (h₁ : FS g₁) (h₂ : FS g₂) (h₃ : FS g₃) (h₄ : FS g₄) (Φ : α → β → γ → δ → ε) :
    FS (fun p => Φ (g₁ p) (g₂ p) (g₃ p) (g₄ p)) :=
  FS.map₂ (FS.map₂ h₁ h₂ Prod.mk) (FS.map₂ h₃ h₄ Prod.mk) (fun x z => Φ x.1 x.2 z.1 z.2)

/-- Shift invariance of the generic ultrafilter, for predicates of finite support. -/
theorem ev_shift {P : Pt → Prop} (hP : FS P) (m : ℤ) :
    (∀ᶠ p in (genW : Filter Pt), P (sh m p.1, p.2)) ↔ ∀ᶠ p in (genW : Filter Pt), P p := by
  have h : FinSupp (fun v D => P (v, D)) := by
    obtain ⟨N, hN⟩ := hP
    exact ⟨N, fun v v' D h => iff_of_eq (hN v v' D h)⟩
  exact ev_sh (P := fun v D => P (v, D)) h m

/-! ## Pre-elements -/

/-- A function of finite support from generic points to the base. -/
structure PreE where
  f : Pt → C
  fin : FS f

theorem PreE.ext {F G : PreE} (h : F.f = G.f) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Shift a pre-element along the sequence of levels. -/
def PreE.shift (m : ℤ) (F : PreE) : PreE where
  f p := F.f (sh m p.1, p.2)
  fin := by
    obtain ⟨N, hN⟩ := F.fin
    exact ⟨N + m.natAbs, fun v v' D h => hN _ _ D fun k hk1 hk2 => h (k + m) (by omega) (by omega)⟩

@[simp] theorem PreE.shift_shift (F : PreE) (a b : ℤ) :
    (F.shift a).shift b = F.shift (a + b) := by
  apply PreE.ext
  funext p
  show F.f (sh a (sh b p.1), p.2) = F.f (sh (a + b) p.1, p.2)
  rw [sh_sh]

@[simp] theorem PreE.shift_zero (F : PreE) : F.shift 0 = F := by
  apply PreE.ext
  funext p
  show F.f (sh 0 p.1, p.2) = F.f p
  rw [sh_zero]

/-- Membership almost everywhere. -/
def EE (F G : PreE) : Prop := ∀ᶠ p in (genW : Filter Pt), E (F.f p) (G.f p)

/-- Equality almost everywhere. -/
def Eqv (F G : PreE) : Prop := ∀ᶠ p in (genW : Filter Pt), F.f p = G.f p

/-- Almost everywhere, `F` has the level of index `k`. -/
def IsLev (k : ℤ) (F : PreE) : Prop := ∀ᶠ p in (genW : Filter Pt), lev (F.f p) = p.1 k

theorem EE_shift (m : ℤ) (F G : PreE) : EE (F.shift m) (G.shift m) ↔ EE F G :=
  ev_shift (P := fun p => E (F.f p) (G.f p)) (FS.map₂ F.fin G.fin E) m

theorem Eqv_shift (m : ℤ) (F G : PreE) : Eqv (F.shift m) (G.shift m) ↔ Eqv F G :=
  ev_shift (P := fun p => F.f p = G.f p) (FS.map₂ F.fin G.fin fun x y => x = y) m

theorem IsLev_shift (k m : ℤ) (F : PreE) : IsLev (k + m) (F.shift m) ↔ IsLev k F :=
  ev_shift (P := fun p => lev (F.f p) = p.1 k)
    (FS.map₂ F.fin (FS.coord k) fun x n => lev x = n) m

theorem IsLev.shift' {F : PreE} (h : IsLev 0 F) (m : ℤ) : IsLev m (F.shift m) := by
  have := (IsLev_shift 0 m F).mpr h
  rwa [zero_add] at this

theorem Eqv.refl (F : PreE) : Eqv F F := Eventually.of_forall fun _ => rfl

theorem Eqv.symm {F G : PreE} (h : Eqv F G) : Eqv G F := h.mono fun _ hp => hp.symm

theorem Eqv.trans {F G H : PreE} (h₁ : Eqv F G) (h₂ : Eqv G H) : Eqv F H := by
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  exact hp₁.trans hp₂

/-- **Witnesses.** A family of predicates of finite support has a pre-element that satisfies the
predicate wherever something does. -/
theorem exists_wit (R : Pt → C → Prop) (hR : FS R) :
    ∃ w : PreE, ∀ p, (∃ a, R p a) → R p (w.f p) := by
  refine ⟨⟨fun p => Classical.epsilon (R p), ?_⟩, fun p h => Classical.epsilon_spec h⟩
  obtain ⟨N, hN⟩ := hR
  refine ⟨N, fun v v' D h => ?_⟩
  show Classical.epsilon (R (v, D)) = Classical.epsilon (R (v', D))
  rw [hN v v' D h]

/-! ## The structure -/

/-- Pre-elements of the level of index 0. -/
def V₀ : Type := {F : PreE // IsLev 0 F}

instance V₀.setoid : Setoid V₀ where
  r x y := Eqv x.1 y.1
  iseqv := ⟨fun x => Eqv.refl x.1, Eqv.symm, Eqv.trans⟩

/-- **The universe of the model.** -/
def V : Type := Quotient V₀.setoid

/-- `x ∈ y`: almost everywhere, `x` is a member of the shift of `y`. -/
def mem₀ (x y : V₀) : Prop := EE x.1 (y.1.shift 1)

theorem mem₀_iff (x y : V₀) (m : ℤ) : mem₀ x y ↔ EE (x.1.shift m) (y.1.shift (1 + m)) := by
  rw [← PreE.shift_shift]
  exact (EE_shift m _ _).symm

theorem mem₀_congr {x x' y y' : V₀} (hx : Eqv x.1 x'.1) (hy : Eqv y.1 y'.1) :
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
def memV : V → V → Prop :=
  Quotient.lift₂ mem₀ fun _ _ _ _ hx hy => propext (mem₀_congr hx hy)

/-- The class of a pre-element. -/
def mk (x : V₀) : V := Quotient.mk V₀.setoid x

theorem memV_mk (x y : V₀) : memV (mk x) (mk y) ↔ mem₀ x y := Iff.rfl

theorem mk_eq_iff {x y : V₀} : mk x = mk y ↔ Eqv x.1 y.1 := Quotient.eq

theorem mk_surj (a : V) : ∃ x, mk x = a := Quotient.exists_rep a

/-- Bring a pre-element of the level of index `k` down to index 0. -/
def lower (k : ℤ) (F : PreE) (h : IsLev k F) : V₀ :=
  ⟨F.shift (-k), by
    have := (IsLev_shift k (-k) F).mpr h
    rwa [add_neg_cancel] at this⟩

theorem lower_shift (k : ℤ) (F : PreE) (h : IsLev k F) : (lower k F h).1.shift k = F := by
  show (F.shift (-k)).shift k = F
  rw [PreE.shift_shift, neg_add_cancel, PreE.shift_zero]

/-! ## Łoś's theorem -/

/-- Satisfaction in the base, where a quantifier of type `t` ranges over the level `ℓ t`. -/
def TSat (ℓ : ℕ → ℕ) : TFm → List C → Prop
  | .mem i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ E a b
  | .eq i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ a = b
  | .neg φ, env => ¬TSat ℓ φ env
  | .and φ ψ, env => TSat ℓ φ env ∧ TSat ℓ ψ env
  | .all t φ, env => ∀ a, lev a = ℓ t → TSat ℓ φ (a :: env)

theorem TSat_congr {ℓ ℓ' : ℕ → ℕ} (φ : TFm) (h : ∀ t, t < φ.bd → ℓ t = ℓ' t) :
    TSat ℓ φ = TSat ℓ' φ := by
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

theorem FS_tsat (φ : TFm) : FS (fun p : Pt => TSat (lvOf p) φ) :=
  ⟨φ.bd, fun _ _ _ h => TSat_congr φ fun t ht => h t (by omega) (by omega)⟩

/-- The values at a generic point of a list of typed pre-elements: the one of type `t` is
shifted to the level of index `t`. -/
def pt (ys : List (ℕ × V₀)) (p : Pt) : List C := ys.map fun y => (y.2.1.shift y.1).f p

theorem FS_pt : ∀ ys : List (ℕ × V₀), FS (pt ys)
  | [] => ⟨0, fun _ _ _ _ => rfl⟩
  | y :: ys => FS.map₂ (y.2.1.shift y.1).fin (FS_pt ys) fun a l => a :: l

theorem ex_some {α : Type*} {u w : α} {R : α → α → Prop} :
    (∃ a b, some u = some a ∧ some w = some b ∧ R a b) ↔ R u w :=
  ⟨fun ⟨a, b, ha, hb, h⟩ => by cases ha; cases hb; exact h, fun h => ⟨u, w, rfl, rfl, h⟩⟩

/-- **Łoś's theorem** for stratified formulas. -/
theorem los (φ : TFm) : ∀ ys : List (ℕ × V₀), TFm.Strat (ys.map Prod.fst) φ →
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
    have hs' : ∀ x : V₀, TFm.Strat (((t, x) :: ys).map Prod.fst) φ := fun _ => hs
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

theorem exists_reps : ∀ (Γ : List ℕ) (params : List V), params.length = Γ.length →
    ∃ ys : List (ℕ × V₀), ys.map Prod.fst = Γ ∧ (ys.map fun y => mk y.2) = params
  | [], [], _ => ⟨[], rfl, rfl⟩
  | t :: Γ, a :: params, h => by
    obtain ⟨ys, h1, h2⟩ := exists_reps Γ params (by simpa using h)
    obtain ⟨x, rfl⟩ := mk_surj a
    exact ⟨(t, x) :: ys, by simp [h1], by simp [h2]⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **Stratified comprehension.** -/
theorem comp_V (t : ℕ) (Γ : List ℕ) (φ : TFm) (hs : TFm.Strat (t :: Γ) φ) (params : List V)
    (hp : params.length = Γ.length) :
    ∃ y : V, ∀ x : V, memV x y ↔ TFm.Sat memV φ (x :: params) := by
  obtain ⟨ys, rfl, rfl⟩ := exists_reps Γ params hp
  have hR : FS (fun (p : Pt) (c : C) => lev c = p.1 ((t + 1 : ℕ) : ℤ) ∧
      ∀ a, lev a = p.1 (t : ℤ) → (E a c ↔ TSat (lvOf p) φ (a :: pt ys p))) :=
    FS.map₄ (FS.coord ((t + 1 : ℕ) : ℤ)) (FS.coord (t : ℤ)) (FS_tsat φ) (FS_pt ys)
      (fun n1 n0 T l => fun c => lev c = n1 ∧ ∀ a, lev a = n0 → (E a c ↔ T (a :: l)))
  obtain ⟨w, hw⟩ := exists_wit _ hR
  have hlt : ∀ᶠ p in (genW : Filter Pt), p.1 (t : ℤ) < p.1 ((t + 1 : ℕ) : ℤ) :=
    ev_lt (by push_cast; omega)
  have hw' : ∀ᶠ p in (genW : Filter Pt), lev (w.f p) = p.1 ((t + 1 : ℕ) : ℤ) ∧
      ∀ a, lev a = p.1 (t : ℤ) → (E a (w.f p) ↔ TSat (lvOf p) φ (a :: pt ys p)) := by
    filter_upwards [hlt] with p hp
    apply hw p
    exact comp_base hp fun a => TSat (lvOf p) φ (a :: pt ys p)
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
theorem ext_V (x y : V) (hne : ∃ z, memV z x) (h : ∀ z, memV z x ↔ memV z y) : x = y := by
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
    exact ext_base h2 h3 ⟨z.1.f p, h5, h4⟩ fun a ha => by_contra fun hiff => hno ⟨a, ha, hiff⟩
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

/-- The members of `c` in the level `n`. -/
def Mems (n : ℕ) (c : C) : Set C := {a | lev a = n ∧ E a c}

/-- **The universe is not finite.** -/
theorem inf_V : UnivInfinite memV := by
  have hR : FS (fun (p : Pt) (c : C) => lev c = p.1 2 ∧
      ∀ y, lev y = p.1 1 → (E y c ↔ (Mems (p.1 0) y).Finite)) :=
    FS.map₃ (FS.coord 2) (FS.coord 1) (FS.coord 0)
      (fun n2 n1 n0 => fun c => lev c = n2 ∧ ∀ y, lev y = n1 → (E y c ↔ (Mems n0 y).Finite))
  obtain ⟨w, hw⟩ := exists_wit _ hR
  have hw' : ∀ᶠ p in (genW : Filter Pt), lev (w.f p) = p.1 2 ∧
      ∀ y, lev y = p.1 1 → (E y (w.f p) ↔ (Mems (p.1 0) y).Finite) := by
    filter_upwards [ev_lt (i := 1) (j := 2) (by norm_num)] with p hp
    apply hw p
    exact comp_base hp fun y => (Mems (p.1 0) y).Finite
  have hlev : IsLev 2 w := hw'.mono fun p hp => hp.1
  -- membership in the family of finite sets
  have memF : ∀ x : V₀, memV (mk x) (mk (lower 2 w hlev)) ↔
      ∀ᶠ p in (genW : Filter Pt), (Mems (p.1 0) ((x.1.shift 1).f p)).Finite := by
    intro x
    rw [memV_mk, mem₀_iff x _ 1]
    have e1 : (lower 2 w hlev).1.shift (1 + 1) = w := by
      rw [show (1 : ℤ) + 1 = 2 by norm_num]
      exact lower_shift _ _ _
    rw [e1]
    have hx : IsLev 1 (x.1.shift 1) := x.2.shift' 1
    constructor
    · intro h
      filter_upwards [h, hw', hx] with p h1 h2 h3
      exact (h2.2 _ h3).mp h1
    · intro h
      filter_upwards [h, hw', hx] with p h1 h2 h3
      exact (h2.2 _ h3).mpr h1
  refine ⟨mk (lower 2 w hlev), ?_, ?_, ?_⟩
  · -- an object without members is finite
    intro e he
    obtain ⟨e, rfl⟩ := mk_surj e
    rw [memF]
    by_contra hcon
    have hcon' : ∀ᶠ p in (genW : Filter Pt), ¬(Mems (p.1 0) ((e.1.shift 1).f p)).Finite :=
      Ultrafilter.eventually_not.mpr hcon
    have hR1 : FS (fun (p : Pt) (a : C) => lev a = p.1 0 ∧ E a ((e.1.shift 1).f p)) :=
      FS.map₂ (FS.coord 0) (e.1.shift 1).fin (fun n X => fun a => lev a = n ∧ E a X)
    obtain ⟨w1, hw1⟩ := exists_wit _ hR1
    have h1 : ∀ᶠ p in (genW : Filter Pt), lev (w1.f p) = p.1 0 ∧ E (w1.f p) ((e.1.shift 1).f p) := by
      filter_upwards [hcon'] with p hp
      apply hw1 p
      by_contra hno
      apply hp
      have e0 : Mems (p.1 0) ((e.1.shift 1).f p) = ∅ :=
        Set.eq_empty_of_forall_notMem fun a ha => hno ⟨a, ha⟩
      rw [e0]
      exact Set.finite_empty
    have hl1 : IsLev 0 w1 := h1.mono fun p hp => hp.1
    exact he (mk ⟨w1, hl1⟩) (h1.mono fun p hp => hp.2)
  · -- adjoining one element to a finite set gives a finite set
    intro a ha b a' hadj
    obtain ⟨a, rfl⟩ := mk_surj a
    obtain ⟨b, rfl⟩ := mk_surj b
    obtain ⟨a', rfl⟩ := mk_surj a'
    rw [memF] at ha ⊢
    by_contra hcon
    have hcon' : ∀ᶠ p in (genW : Filter Pt), ¬(Mems (p.1 0) ((a'.1.shift 1).f p)).Finite :=
      Ultrafilter.eventually_not.mpr hcon
    have hR2 : FS (fun (p : Pt) (c : C) => lev c = p.1 0 ∧ E c ((a'.1.shift 1).f p) ∧
        ¬E c ((a.1.shift 1).f p) ∧ c ≠ b.1.f p) :=
      FS.map₄ (FS.coord 0) (a'.1.shift 1).fin (a.1.shift 1).fin b.1.fin
        (fun n X Y B => fun c => lev c = n ∧ E c X ∧ ¬E c Y ∧ c ≠ B)
    obtain ⟨w2, hw2⟩ := exists_wit _ hR2
    have h2 : ∀ᶠ p in (genW : Filter Pt), lev (w2.f p) = p.1 0 ∧
        E (w2.f p) ((a'.1.shift 1).f p) ∧ ¬E (w2.f p) ((a.1.shift 1).f p) ∧ w2.f p ≠ b.1.f p := by
      filter_upwards [hcon', ha] with p hp hfin
      apply hw2 p
      by_contra hno
      apply hp
      refine (hfin.union (Set.finite_singleton (b.1.f p))).subset fun c hc => ?_
      by_contra hc'
      simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hc'
      exact hno ⟨c, hc.1, hc.2, fun hE => hc'.1 ⟨hc.1, hE⟩, hc'.2⟩
    have hl2 : IsLev 0 w2 := h2.mono fun p hp => hp.1
    have hm : memV (mk ⟨w2, hl2⟩) (mk a') := h2.mono fun p hp => hp.2.1
    rcases (hadj (mk ⟨w2, hl2⟩)).mp hm with h3 | h3
    · have h3' : ∀ᶠ p in (genW : Filter Pt), E (w2.f p) ((a.1.shift 1).f p) := h3
      obtain ⟨p, hp1, hp2⟩ := (h2.and h3').exists
      exact hp1.2.2.1 hp2
    · have h3' : ∀ᶠ p in (genW : Filter Pt), w2.f p = b.1.f p := mk_eq_iff.mp h3
      obtain ⟨p, hp1, hp2⟩ := (h2.and h3').exists
      exact hp1.2.2.2 hp2
  · -- a universal set is not finite
    intro u hu huF
    obtain ⟨u, rfl⟩ := mk_surj u
    rw [memF] at huF
    have hR3 : FS (fun (p : Pt) (a : C) => lev a = p.1 0 ∧ ¬E a ((u.1.shift 1).f p)) :=
      FS.map₂ (FS.coord 0) (u.1.shift 1).fin (fun n X => fun a => lev a = n ∧ ¬E a X)
    obtain ⟨w3, hw3⟩ := exists_wit _ hR3
    have h3 : ∀ᶠ p in (genW : Filter Pt), lev (w3.f p) = p.1 0 ∧ ¬E (w3.f p) ((u.1.shift 1).f p) := by
      filter_upwards [huF] with p hfin
      apply hw3 p
      obtain ⟨a, ha1, ha2⟩ := ((inf_base (p.1 0)).sdiff hfin).nonempty
      exact ⟨a, ha1, fun hE => ha2 ⟨ha1, hE⟩⟩
    have hl3 : IsLev 0 w3 := h3.mono fun p hp => hp.1
    have h4 : ∀ᶠ p in (genW : Filter Pt), E (w3.f p) ((u.1.shift 1).f p) := hu (mk ⟨w3, hl3⟩)
    obtain ⟨p, hp1, hp2⟩ := (h3.and h4).exists
    exact hp1.2 hp2

/-- The structure `(V, memV)` satisfies NFU. -/
theorem isNFU_V : IsNFU V memV := ⟨ext_V, comp_V⟩

/-- **There is a model of NFU in which the universe is not finite.** -/
theorem exists_model : ∃ (V : Type) (mem : V → V → Prop), IsNFU V mem ∧ UnivInfinite mem :=
  ⟨V, memV, isNFU_V, inf_V⟩

end JensenNFU
