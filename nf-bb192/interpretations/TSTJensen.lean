import TSTTheories
import JensenGeneric
import NFUConsistent

set_option autoImplicit false

/-!
# From a model of `𝗧𝗦𝗧𝗜` to a model of `𝗡𝗙𝗨𝗜` (Jensen)

Fix a model `M` of `𝗧𝗦𝗧𝗜`. This file shows that its types form a base in the sense of
`JensenGeneric.lean`, and concludes that there is a model of `𝗡𝗙𝗨𝗜`.

* **Membership between levels that are not adjacent.** For `a < b`, an object `y` of type `b`
  is the *code* of the object `S` of type `a + 1` if `y` is the iterated singleton
  `{{…{S}…}}` (`Iota`). Then `x E y`, for `x` of type `a`, means that `y` is the code of some `S`
  with `x ∈ S` (`SMem`). An object of type `b` that is not a code has no members of type `a`: it
  is an urelement.
* **These relations are definable in `M`**, by the typed formulas `iotaF` and `smemF`. So a typed
  formula about the levels `ℓ 0 < ℓ 1 < …` with the relation `E` can be rewritten as a typed
  formula of `M` (`skip`, `holds_skip`), and comprehension in `M` gives comprehension in the
  base (`comp_base'`).
* **Extensionality** for objects with members: `ext_base'`.
* **Infinity.** The universe of every type is not finite (`inf_all`, from the axiom for type 0,
  by passing from a family of sets to the family of their images under `x ↦ {x}`). The
  objects of level `ℓ 1` whose extension is in a given family form a set, and its code is the
  family needed in the base (`inf_base'`).
* **Result**: `exists_nfui_model`.
-/

namespace FFL.FirstOrder

namespace TST

open JensenNFU (TFm)
open JensenNFU.Gen (JBase₀ JBase TSat tsat_iff_satT)

variable {M : Type} [s : Tarski.Structure ℒₜₛₜ M] [Tarski.Structure.Eq ℒₜₛₜ M] [Nonempty M]
  [hM : M↓[ℒₜₛₜ] ⊧* 𝗧𝗦𝗧𝗜]

/-! ### Three instances of comprehension -/

/-- Singletons. -/
theorem exists_sing {m : ℕ} {z : M} (hz : Ty m z) :
    ∃ y, Ty (m + 1) y ∧ ∀ w, Ty m w → (Mem w y ↔ w = z) := by
  obtain ⟨y, hy, h⟩ := comp hM (t := m) (Γ := [m]) (φ := .eq 0 1)
    (TFm.strat_eq (t := m) rfl rfl) (fun _ => z)
    (by intro i hi; have : i = 0 := by simpa using hi
        subst this; exact hz)
  exact ⟨y, hy, fun w hw => by simpa using h w hw⟩

/-- The empty set of each type. -/
theorem exists_empty (m : ℕ) : ∃ y : M, Ty (m + 1) y ∧ ∀ w, Ty m w → ¬Mem w y := by
  obtain ⟨y, hy, h⟩ := comp hM (t := m) (Γ := []) (φ := .neg (.eq 0 0))
    (TFm.strat_eq (t := m) rfl rfl) (fun _ => Classical.arbitrary M)
    (by intro i hi; simp at hi)
  exact ⟨y, hy, fun w hw => by simpa using h w hw⟩

/-- Adjoining one element. -/
theorem exists_adjoin {m : ℕ} {A b : M} (hA : Ty (m + 1) A) (hb : Ty m b) :
    ∃ A', Ty (m + 1) A' ∧ ∀ w, Ty m w → (Mem w A' ↔ Mem w A ∨ w = b) := by
  obtain ⟨y, hy, h⟩ := comp hM (t := m) (Γ := [m + 1, m]) (φ := TFm.or (.mem 0 1) (.eq 0 2))
    ⟨TFm.strat_mem (t := m) rfl rfl, TFm.strat_eq (t := m) rfl rfl⟩
    (TFm.scons A (TFm.scons b (fun _ => b)))
    (by intro i hi
        have hi' : i < 2 := by simpa using hi
        interval_cases i
        · exact hA
        · exact hb)
  exact ⟨y, hy, fun w hw => by simpa using h w hw⟩

/-! ### Iterated singletons -/

/-- `y` is the `d`-fold singleton of `S`. If `S` has type `k`, then `y` has type `k + d`. -/
def Iota (k : ℕ) : ℕ → M → M → Prop
  | 0, S, y => y = S
  | d + 1, S, y => ∃ z, Ty (k + d) z ∧ Iota k d S z ∧ ∀ w, Ty (k + d) w → (Mem w y ↔ w = z)

/-- The typed formula for `Iota`: the variable `j` is the `d`-fold singleton of the variable
`i`. -/
def iotaF (k : ℕ) : ℕ → ℕ → ℕ → TFm
  | 0, i, j => .eq j i
  | d + 1, i, j => TFm.ex (k + d) (.and (iotaF k d (i + 1) 0)
      (.all (k + d) (TFm.iff (.mem 0 (j + 2)) (.eq 0 1))))

omit [Tarski.Structure.Eq ℒₜₛₜ M] [Nonempty M] hM in
theorem holds_iotaF (k : ℕ) : ∀ (d i j : ℕ) (v : ℕ → M),
    Holds (iotaF k d i j) v ↔ Iota k d (v i) (v j)
  | 0, i, j, v => by simp [iotaF, Iota]
  | d + 1, i, j, v => by
    simp only [iotaF, TFm.satT_ex, TFm.satT_and, holds_iotaF k d, TFm.satT_all, TFm.satT_iff,
      TFm.satT_mem, TFm.satT_eq, TFm.scons_zero, TFm.scons_succ, Iota]

theorem strat_iotaF (k : ℕ) : ∀ (d i j : ℕ) (Γ : List ℕ), Γ[i]? = some k →
    Γ[j]? = some (k + d) → TFm.Strat Γ (iotaF k d i j)
  | 0, _, _, _, hi, hj => TFm.strat_eq hj hi
  | d + 1, i, j, Γ, hi, hj => by
    simp only [iotaF, TFm.strat_ex, TFm.strat_and, TFm.strat_all, TFm.strat_iff]
    refine ⟨strat_iotaF k d (i + 1) 0 _ (by rw [List.getElem?_cons_succ]; exact hi) rfl, ?_, ?_⟩
    · exact TFm.strat_mem (t := k + d) rfl
        (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact hj)
    · exact TFm.strat_eq (t := k + d) rfl rfl

theorem iota_exists (k : ℕ) {S : M} (hS : Ty k S) : ∀ d, ∃ y, Ty (k + d) y ∧ Iota k d S y
  | 0 => ⟨S, hS, rfl⟩
  | d + 1 => by
    obtain ⟨z, hz, hι⟩ := iota_exists k hS d
    obtain ⟨y, hy, h⟩ := exists_sing (M := M) hz
    exact ⟨y, hy, z, hz, hι, h⟩

theorem iota_fun (k : ℕ) {S : M} : ∀ (d : ℕ) {y y' : M}, Iota k d S y → Iota k d S y' →
    Ty (k + d) y → Ty (k + d) y' → y = y'
  | 0, _, _, h, h', _, _ => h.trans h'.symm
  | d + 1, _, _, ⟨z, hz, hι, h⟩, ⟨z', hz', hι', h'⟩, hy, hy' => by
    have e : z = z' := iota_fun k d hι hι' hz hz'
    subst e
    exact ext hM (n := k + d) hy hy' fun w hw => (h w hw).trans (h' w hw).symm

omit [Tarski.Structure.Eq ℒₜₛₜ M] [Nonempty M] hM in
theorem iota_inj (k : ℕ) : ∀ (d : ℕ) {S S' y : M}, Iota k d S y → Iota k d S' y → S = S'
  | 0, _, _, _, h, h' => h.symm.trans h'
  | d + 1, _, _, _, ⟨z, hz, hι, h⟩, ⟨z', _, hι', h'⟩ => by
    have e : z = z' := (h' z hz).mp ((h z hz).mpr rfl)
    subst e
    exact iota_inj k d hι hι'

/-! ### Membership between two levels -/

/-- `x`, of type `a`, is a member of `y`, of type `a + 1 + d`: `y` is the `d`-fold singleton of
an object of type `a + 1` that has `x` as a member. -/
def SMem (a d : ℕ) (x y : M) : Prop := ∃ S, Ty (a + 1) S ∧ Mem x S ∧ Iota (a + 1) d S y

/-- The typed formula for `SMem`. -/
def smemF (a d i j : ℕ) : TFm :=
  TFm.ex (a + 1) (.and (.mem (i + 1) 0) (iotaF (a + 1) d 0 (j + 1)))

omit [Tarski.Structure.Eq ℒₜₛₜ M] [Nonempty M] hM in
theorem holds_smemF (a d i j : ℕ) (v : ℕ → M) :
    Holds (smemF a d i j) v ↔ SMem a d (v i) (v j) := by
  simp only [smemF, TFm.satT_ex, TFm.satT_and, TFm.satT_mem, holds_iotaF, TFm.scons_zero,
    TFm.scons_succ, SMem]

theorem strat_smemF {a d i j : ℕ} {Γ : List ℕ} (hi : Γ[i]? = some a)
    (hj : Γ[j]? = some (a + 1 + d)) : TFm.Strat Γ (smemF a d i j) := by
  simp only [smemF, TFm.strat_ex, TFm.strat_and]
  exact ⟨TFm.strat_mem (t := a) (by rw [List.getElem?_cons_succ]; exact hi) rfl,
    strat_iotaF (a + 1) d 0 (j + 1) _ rfl (by rw [List.getElem?_cons_succ]; exact hj)⟩

/-! ### The base -/

/-- The carrier of the base: an object of `M` together with a type that it has. -/
abbrev Car (M : Type) [Tarski.Structure ℒₜₛₜ M] : Type := Σ n : ℕ, {x : M // Ty n x}

omit [Tarski.Structure.Eq ℒₜₛₜ M] [Nonempty M] hM in
theorem car_ext {a b : Car M} (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) : a = b := by
  obtain ⟨n, x, hx⟩ := a
  obtain ⟨n', x', hx'⟩ := b
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- The level of an object is its type; `x E y` if the level of `x` is below that of `y` and
`x` is a member of `y` in the sense of `SMem`. -/
instance base₀ : JBase₀ (Car M) where
  lev x := x.1
  E x y := x.1 < y.1 ∧ SMem x.1 (y.1 - x.1 - 1) x.2.1 y.2.1
  ne := by
    obtain ⟨y, hy, -⟩ := exists_empty (M := M) 0
    exact ⟨⟨1, y, hy⟩⟩

local notation "E'" => JensenNFU.Gen.E

theorem E_iff_smem {x y : Car M} {a b : ℕ} (hx : x.1 = a) (hy : y.1 = b) (hab : a < b) :
    E' x y ↔ SMem a (b - a - 1) x.2.1 y.2.1 := by
  obtain ⟨n, x₀, hx₀⟩ := x
  obtain ⟨m, y₀, hy₀⟩ := y
  simp only at hx hy
  subst hx
  subst hy
  exact ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩

/-- Every object of type `a + 1` has a code in each level `b > a`. -/
theorem exists_code {a b : ℕ} (hab : a < b) {S : M} (hS : Ty (a + 1) S) :
    ∃ c : Car M, c.1 = b ∧ Iota (a + 1) (b - a - 1) S c.2.1 := by
  obtain ⟨y, hy, hι⟩ := iota_exists (M := M) (a + 1) hS (b - a - 1)
  have e : a + 1 + (b - a - 1) = b := by omega
  exact ⟨⟨b, y, e ▸ hy⟩, rfl, hι⟩

/-- The members of a code, in the sense of `E`, are the members of the object it codes. -/
theorem E_code {a b : ℕ} (hab : a < b) {S : M} (hS : Ty (a + 1) S) {c : Car M} (hc : c.1 = b)
    (hι : Iota (a + 1) (b - a - 1) S c.2.1) (x : Car M) (hx : x.1 = a) :
    E' x c ↔ Mem x.2.1 S := by
  rw [E_iff_smem hx hc hab]
  constructor
  · rintro ⟨S', -, hxS', hι'⟩
    rw [iota_inj _ _ hι hι']
    exact hxS'
  · intro h
    exact ⟨S, hS, h, hι⟩

/-- **Extensionality in the base**, for objects with members. -/
theorem ext_base' {a b : ℕ} {y y' : Car M} (hy : y.1 = b) (hy' : y'.1 = b)
    (hne : ∃ x : Car M, x.1 = a ∧ E' x y) (hmem : ∀ x : Car M, x.1 = a → (E' x y ↔ E' x y')) :
    y = y' := by
  obtain ⟨x, hxa, hxy⟩ := hne
  have hab : a < b := by
    have := hxy.1
    rw [hxa, hy] at this
    exact this
  obtain ⟨S, hS, -, hι⟩ := (E_iff_smem hxa hy hab).mp hxy
  obtain ⟨S', hS', -, hι'⟩ := (E_iff_smem hxa hy' hab).mp ((hmem x hxa).mp hxy)
  have hSS : S = S' := by
    refine ext hM hS hS' fun z hz => ?_
    have hz1 := E_code hab hS hy hι ⟨a, z, hz⟩ rfl
    have hz2 := E_code hab hS' hy' hι' ⟨a, z, hz⟩ rfl
    exact hz1.symm.trans ((hmem ⟨a, z, hz⟩ rfl).trans hz2)
  subst hSS
  have e : a + 1 + (b - a - 1) = b := by omega
  refine car_ext (hy.trans hy'.symm) (iota_fun (a + 1) (b - a - 1) hι hι' ?_ ?_)
  · rw [e, ← hy]; exact y.2.2
  · rw [e, ← hy']; exact y'.2.2

/-! ### Typed formulas along a sequence of levels -/

/-- Rewrite a typed formula about the levels `ℓ 0, ℓ 1, …` as a typed formula of `M`: a
quantifier of type `t` becomes one of type `ℓ t`, and `x ∈ y` with `x` of type `t` becomes
membership between the levels `ℓ t` and `ℓ (t + 1)`. `Γ` lists the types of the free variables. -/
def skip (ℓ : ℕ → ℕ) : List ℕ → TFm → TFm
  | Γ, .mem i j => smemF (ℓ (Γ.getD i 0)) (ℓ (Γ.getD i 0 + 1) - ℓ (Γ.getD i 0) - 1) i j
  | _, .eq i j => .eq i j
  | Γ, .neg φ => .neg (skip ℓ Γ φ)
  | Γ, .and φ ψ => .and (skip ℓ Γ φ) (skip ℓ Γ ψ)
  | Γ, .all t φ => .all (ℓ t) (skip ℓ (t :: Γ) φ)

theorem strat_skip {ℓ : ℕ → ℕ} (hℓ : StrictMono ℓ) (φ : TFm) :
    ∀ Γ : List ℕ, TFm.Strat Γ φ → TFm.Strat (Γ.map ℓ) (skip ℓ Γ φ) := by
  induction φ with
  | mem i j =>
    rintro Γ ⟨t, hi, hj⟩
    have hgi : Γ.getD i 0 = t := by rw [List.getD_eq_getElem?_getD, hi]; rfl
    simp only [skip, hgi]
    have hlt := hℓ (Nat.lt_add_one t)
    refine strat_smemF (by rw [List.getElem?_map, hi]; rfl) ?_
    rw [List.getElem?_map, hj]
    show some (ℓ (t + 1)) = some (ℓ t + 1 + (ℓ (t + 1) - ℓ t - 1))
    congr 1
    omega
  | eq i j =>
    rintro Γ ⟨t, hi, hj⟩
    exact TFm.strat_eq (t := ℓ t) (by rw [List.getElem?_map, hi]; rfl)
      (by rw [List.getElem?_map, hj]; rfl)
  | neg φ ih => intro Γ h; simp only [skip]; exact ih Γ h
  | and φ ψ ih1 ih2 => intro Γ h; simp only [skip]; exact ⟨ih1 Γ h.1, ih2 Γ h.2⟩
  | all t φ ih => intro Γ h; simp only [skip]; exact ih (t :: Γ) h

/-- The rewritten formula holds in `M` iff the original one holds in the base along `ℓ`. -/
theorem holds_skip {ℓ : ℕ → ℕ} (hℓ : StrictMono ℓ) (φ : TFm) :
    ∀ (Γ : List ℕ) (w : ℕ → Car M), TFm.Strat Γ φ →
      (∀ i (h : i < Γ.length), (w i).1 = ℓ Γ[i]) →
      (TFm.SatT (fun t (c : Car M) => JensenNFU.Gen.lev c = ℓ t) E' φ w ↔
        Holds (skip ℓ Γ φ) (fun i => (w i).2.1)) := by
  induction φ with
  | mem i j =>
    rintro Γ w ⟨t, hi, hj⟩ hw
    obtain ⟨hi', hti⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', htj⟩ := List.getElem?_eq_some_iff.mp hj
    have hgi : Γ.getD i 0 = t := by rw [List.getD_eq_getElem?_getD, hi]; rfl
    have h1 : (w i).1 = ℓ t := by rw [hw i hi', hti]
    have h2 : (w j).1 = ℓ (t + 1) := by rw [hw j hj', htj]
    simp only [TFm.satT_mem, skip, hgi, holds_smemF]
    exact E_iff_smem h1 h2 (hℓ (Nat.lt_add_one t))
  | eq i j =>
    rintro Γ w ⟨t, hi, hj⟩ hw
    obtain ⟨hi', hti⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', htj⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [TFm.satT_eq, skip]
    constructor
    · intro h; rw [h]
    · intro h; exact car_ext (by rw [hw i hi', hw j hj', hti, htj]) h
  | neg φ ih => intro Γ w hs hw; simp only [TFm.satT_neg, skip, ih Γ w hs hw]
  | and φ ψ ih1 ih2 =>
    intro Γ w hs hw; simp only [TFm.satT_and, skip, ih1 Γ w hs.1 hw, ih2 Γ w hs.2 hw]
  | all t φ ih =>
    intro Γ w hs hw
    simp only [TFm.satT_all, skip]
    have hw' : ∀ (c : Car M), c.1 = ℓ t → ∀ i (h : i < (t :: Γ).length),
        (TFm.scons c w i).1 = ℓ ((t :: Γ).get ⟨i, h⟩) := by
      intro c hc i hi
      cases i with
      | zero => exact hc
      | succ i => exact hw i (by simpa using hi)
    have e : ∀ (x : M) (hx : Ty (ℓ t) x),
        (fun i => (TFm.scons (⟨ℓ t, x, hx⟩ : Car M) w i).2.1) =
          TFm.scons x (fun i => (w i).2.1) := by
      intro x hx
      funext i
      cases i <;> rfl
    constructor
    · intro h x hx
      have := (ih (t :: Γ) (TFm.scons (⟨ℓ t, x, hx⟩ : Car M) w) hs (hw' _ rfl)).mp
        (h ⟨ℓ t, x, hx⟩ rfl)
      rwa [e x hx] at this
    · intro h a ha
      obtain ⟨n, x, hx⟩ := a
      have ha' : n = ℓ t := ha
      subst ha'
      refine (ih (t :: Γ) (TFm.scons (⟨ℓ t, x, hx⟩ : Car M) w) hs (hw' _ rfl)).mpr ?_
      rw [e x hx]
      exact h x hx

/-- **Comprehension in the base**, for well typed formulas. -/
theorem comp_base' (ℓ : ℕ → ℕ) (hℓ : StrictMono ℓ) (t : ℕ) (Γ : List ℕ) (φ : TFm)
    (hφ : TFm.Strat (t :: Γ) φ) (env : List (Car M))
    (henv : List.Forall₂ (fun s (c : Car M) => c.1 = ℓ s) Γ env) :
    ∃ c : Car M, c.1 = ℓ (t + 1) ∧ ∀ x : Car M, x.1 = ℓ t → (E' x c ↔ TSat ℓ φ (x :: env)) := by
  obtain ⟨d⟩ := (JBase₀.ne : Nonempty (Car M))
  have hlen : env.length = Γ.length := henv.length_eq.symm
  have hlev : ∀ i (h : i < Γ.length), (env.getD i d).1 = ℓ Γ[i] := by
    intro i h
    have h' : i < env.length := hlen ▸ h
    rw [List.getD_eq_getElem _ _ h']
    exact (List.forall₂_iff_get.mp henv).2 i h h'
  obtain ⟨S, hS, hSmem⟩ := comp hM (t := ℓ t) (Γ := Γ.map ℓ) (φ := skip ℓ (t :: Γ) φ)
    (strat_skip hℓ φ (t :: Γ) hφ) (fun i => (env.getD i d).2.1) (by
      intro i hi
      have hi' : i < Γ.length := by simpa using hi
      rw [List.getElem_map, ← hlev i hi']
      exact (env.getD i d).2.2)
  have hlt : ℓ t < ℓ (t + 1) := hℓ (Nat.lt_add_one t)
  obtain ⟨c, hc, hι⟩ := exists_code hlt hS
  refine ⟨c, hc, fun x hx => ?_⟩
  rw [E_code hlt hS hc hι x hx]
  obtain ⟨n, x₀, hx₀⟩ := x
  have hx' : n = ℓ t := hx
  subst hx'
  rw [hSmem x₀ hx₀, tsat_iff_satT d ℓ φ (t :: Γ) _ hφ (by simp [hlen])]
  have key := holds_skip hℓ φ (t :: Γ)
    (TFm.scons (⟨ℓ t, x₀, hx₀⟩ : Car M) (fun i => env.getD i d)) hφ (by
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact hlev i (by simpa using hi))
  have e1 : (fun i => ((⟨ℓ t, x₀, hx₀⟩ : Car M) :: env).getD i d) =
      TFm.scons (⟨ℓ t, x₀, hx₀⟩ : Car M) (fun i => env.getD i d) := by
    funext i
    cases i <;> simp
  have e2 : (fun i => (TFm.scons (⟨ℓ t, x₀, hx₀⟩ : Car M) (fun i => env.getD i d) i).2.1) =
      TFm.scons x₀ (fun i => (env.getD i d).2.1) := by
    funext i
    cases i <;> rfl
  rw [e1, key, e2]

/-! ### Infinity -/

/-- **The universe of every type is not finite.** -/
theorem inf_all : ∀ (k : ℕ) (v : ℕ → M), Holds (TFm.infFm k) v
  | 0, v => inf hM v
  | k + 1, v => by
    obtain ⟨G, hG, hG1, hG2, hG3⟩ := TFm.satT_infFm.mp (inf_all k v)
    obtain ⟨G', hG', hmem⟩ := comp hM (t := k + 2) (Γ := [k + 2])
      (φ := TFm.ex (k + 1) (.and (.all k (TFm.iff (.mem 0 1)
        (TFm.ex (k + 1) (.and (.all k (TFm.iff (.mem 0 1) (.eq 0 2))) (.mem 0 3)))))
        (.mem 0 2)))
      (by
        simp only [TFm.strat_ex, TFm.strat_and, TFm.strat_all, TFm.strat_iff]
        exact ⟨⟨TFm.strat_mem (t := k) rfl rfl, ⟨TFm.strat_mem (t := k) rfl rfl,
          TFm.strat_eq (t := k) rfl rfl⟩, TFm.strat_mem (t := k + 1) rfl rfl⟩,
          TFm.strat_mem (t := k + 1) rfl rfl⟩)
      (fun _ => G)
      (by intro i hi; have : i = 0 := by simpa using hi
          subst this; exact hG)
    have hmem' : ∀ B, Ty (k + 2) B → (Mem B G' ↔ ∃ A, Ty (k + 1) A ∧
        (∀ x, Ty k x → (Mem x A ↔ ∃ s₁, Ty (k + 1) s₁ ∧
          (∀ w, Ty k w → (Mem w s₁ ↔ w = x)) ∧ Mem s₁ B)) ∧ Mem A G) := by
      intro B hB
      simpa using hmem B hB
    refine TFm.satT_infFm.mpr ⟨G', hG', ?_, ?_, ?_⟩
    · intro e he hemp
      obtain ⟨A, hA, hAemp⟩ := exists_empty (M := M) k
      refine (hmem' e he).mpr ⟨A, hA, fun x hx => ⟨fun h => absurd h (hAemp x hx), ?_⟩,
        hG1 A hA hAemp⟩
      rintro ⟨s₁, hs₁, -, hs₁e⟩
      exact absurd hs₁e (hemp s₁ hs₁)
    · intro s₁ hs₁ hs₁G b hb s₁' hs₁' hadj
      obtain ⟨A, hA, hAiff, hAG⟩ := (hmem' s₁ hs₁).mp hs₁G
      by_cases hsing : ∃ x₀, Ty k x₀ ∧ ∀ w, Ty k w → (Mem w b ↔ w = x₀)
      · obtain ⟨x₀, hx₀, hbx₀⟩ := hsing
        obtain ⟨A', hA', hA'iff⟩ := exists_adjoin (M := M) hA hx₀
        refine (hmem' s₁' hs₁').mpr ⟨A', hA', fun x hx => ?_,
          hG2 A hA hAG x₀ hx₀ A' hA' hA'iff⟩
        rw [hA'iff x hx, hAiff x hx]
        constructor
        · rintro (⟨s₂, hs₂, hs₂x, hs₂s₁⟩ | hxx₀)
          · exact ⟨s₂, hs₂, hs₂x, (hadj s₂ hs₂).mpr (Or.inl hs₂s₁)⟩
          · exact ⟨b, hb, hxx₀ ▸ hbx₀, (hadj b hb).mpr (Or.inr rfl)⟩
        · rintro ⟨s₂, hs₂, hs₂x, hs₂s₁'⟩
          rcases (hadj s₂ hs₂).mp hs₂s₁' with h | h
          · exact Or.inl ⟨s₂, hs₂, hs₂x, h⟩
          · exact Or.inr ((hbx₀ x hx).mp (h ▸ (hs₂x x hx).mpr rfl))
      · refine (hmem' s₁' hs₁').mpr ⟨A, hA, fun x hx => ?_, hAG⟩
        rw [hAiff x hx]
        constructor
        · rintro ⟨s₂, hs₂, hs₂x, hs₂s₁⟩
          exact ⟨s₂, hs₂, hs₂x, (hadj s₂ hs₂).mpr (Or.inl hs₂s₁)⟩
        · rintro ⟨s₂, hs₂, hs₂x, hs₂s₁'⟩
          rcases (hadj s₂ hs₂).mp hs₂s₁' with h | h
          · exact ⟨s₂, hs₂, hs₂x, h⟩
          · exact absurd ⟨x, hx, h ▸ hs₂x⟩ hsing
    · intro u hu huall huG
      obtain ⟨A, hA, hAiff, hAG⟩ := (hmem' u hu).mp huG
      refine hG3 A hA (fun x hx => ?_) hAG
      obtain ⟨s₁, hs₁, hs₁x⟩ := exists_sing (M := M) hx
      exact (hAiff x hx).mpr ⟨s₁, hs₁, hs₁x, huall s₁ hs₁⟩

/-- **Infinity in the base**: along every strictly increasing sequence of levels, the universe
of type 0 is not finite. -/
theorem inf_base' (ℓ : ℕ → ℕ) (hℓ : StrictMono ℓ) : TSat (C := Car M) ℓ (TFm.infFm 0) [] := by
  obtain ⟨d⟩ := (JBase₀.ne : Nonempty (Car M))
  rw [tsat_iff_satT d ℓ (TFm.infFm 0) [] [] (TFm.strat_infFm 0 []) rfl, TFm.satT_infFm]
  have h01 : ℓ 0 < ℓ 1 := hℓ (by norm_num)
  have h12 : ℓ 1 < ℓ 2 := hℓ (by norm_num)
  obtain ⟨G, hG, hG1, hG2, hG3⟩ :=
    TFm.satT_infFm.mp (inf_all (M := M) (ℓ 0) (fun _ => Classical.arbitrary M))
  have e₁ : ℓ 0 + 1 + (ℓ 1 - ℓ 0 - 1) = ℓ 1 := by omega
  obtain ⟨S, hS, hSmem⟩ := comp hM (t := ℓ 0 + 1 + (ℓ 1 - ℓ 0 - 1)) (Γ := [ℓ 0 + 2])
    (φ := TFm.ex (ℓ 0 + 1) (.and (.all (ℓ 0) (TFm.iff (.mem 0 1)
      (smemF (ℓ 0) (ℓ 1 - ℓ 0 - 1) 0 2))) (.mem 0 2)))
    (by
      simp only [TFm.strat_ex, TFm.strat_and, TFm.strat_all, TFm.strat_iff]
      exact ⟨⟨TFm.strat_mem (t := ℓ 0) rfl rfl, strat_smemF rfl rfl⟩,
        TFm.strat_mem (t := ℓ 0 + 1) rfl rfl⟩)
    (fun _ => G)
    (by intro i hi; have : i = 0 := by simpa using hi
        subst this; exact hG)
  rw [e₁] at hS hSmem
  have hSmem' : ∀ y, Ty (ℓ 1) y → (Mem y S ↔ ∃ A, Ty (ℓ 0 + 1) A ∧
      (∀ x, Ty (ℓ 0) x → (Mem x A ↔ SMem (ℓ 0) (ℓ 1 - ℓ 0 - 1) x y)) ∧ Mem A G) := by
    intro y hy
    simpa [holds_smemF] using hSmem y hy
  obtain ⟨F, hF, hι⟩ := exists_code h12 hS
  have hEF : ∀ e : Car M, e.1 = ℓ 1 → (E' e F ↔ Mem e.2.1 S) := E_code h12 hS hF hι
  have hE01 : ∀ (z e : Car M), z.1 = ℓ 0 → e.1 = ℓ 1 →
      (E' z e ↔ SMem (ℓ 0) (ℓ 1 - ℓ 0 - 1) z.2.1 e.2.1) := fun z e hz he => E_iff_smem hz he h01
  have hty1 : ∀ e : Car M, e.1 = ℓ 1 → Ty (ℓ 1) e.2.1 := fun e he => he ▸ e.2.2
  have hty0 : ∀ z : Car M, z.1 = ℓ 0 → Ty (ℓ 0) z.2.1 := fun z hz => hz ▸ z.2.2
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro e he hemp
    obtain ⟨A, hA, hAemp⟩ := exists_empty (M := M) (ℓ 0)
    refine (hEF e he).mpr ((hSmem' _ (hty1 e he)).mpr ⟨A, hA, fun x hx =>
      ⟨fun h => absurd h (hAemp x hx), fun h => ?_⟩, hG1 A hA hAemp⟩)
    exact absurd ((hE01 ⟨ℓ 0, x, hx⟩ e rfl he).mpr h) (hemp ⟨ℓ 0, x, hx⟩ rfl)
  · intro s₁ hs₁ hs₁F b hb s₁' hs₁' hadj
    obtain ⟨A, hA, hAiff, hAG⟩ := (hSmem' _ (hty1 s₁ hs₁)).mp ((hEF s₁ hs₁).mp hs₁F)
    obtain ⟨A', hA', hA'iff⟩ := exists_adjoin (M := M) hA (hty0 b hb)
    refine (hEF s₁' hs₁').mpr ((hSmem' _ (hty1 s₁' hs₁')).mpr ⟨A', hA', fun x hx => ?_,
      hG2 A hA hAG _ (hty0 b hb) A' hA' hA'iff⟩)
    calc Mem x A' ↔ Mem x A ∨ x = b.2.1 := hA'iff x hx
      _ ↔ SMem (ℓ 0) (ℓ 1 - ℓ 0 - 1) x s₁.2.1 ∨ x = b.2.1 := or_congr (hAiff x hx) Iff.rfl
      _ ↔ E' (⟨ℓ 0, x, hx⟩ : Car M) s₁ ∨ (⟨ℓ 0, x, hx⟩ : Car M) = b :=
        or_congr (hE01 ⟨ℓ 0, x, hx⟩ s₁ rfl hs₁).symm
          ⟨fun h => car_ext (Eq.symm hb) h, fun h => by rw [← h]⟩
      _ ↔ E' (⟨ℓ 0, x, hx⟩ : Car M) s₁' := (hadj ⟨ℓ 0, x, hx⟩ rfl).symm
      _ ↔ SMem (ℓ 0) (ℓ 1 - ℓ 0 - 1) x s₁'.2.1 := hE01 ⟨ℓ 0, x, hx⟩ s₁' rfl hs₁'
  · intro u hu huall huF
    obtain ⟨A, hA, hAiff, hAG⟩ := (hSmem' _ (hty1 u hu)).mp ((hEF u hu).mp huF)
    exact hG3 A hA (fun x hx => (hAiff x hx).mpr
      ((hE01 ⟨ℓ 0, x, hx⟩ u rfl hu).mp (huall ⟨ℓ 0, x, hx⟩ rfl))) hAG

/-- **The types of a model of `𝗧𝗦𝗧𝗜` form a base.** -/
instance base : JBase (Car M) where
  toJBase₀ := base₀
  ext_base := fun hy hy' hne hmem => ext_base' hy hy' hne hmem
  comp_base := comp_base'
  inf_base := inf_base'

/-! ### The theorem -/

/-- **Jensen's theorem, over an arbitrary model of `𝗧𝗦𝗧𝗜`.** If `M` is a model of `𝗧𝗦𝗧𝗜`, there
is a model `N` of `𝗡𝗙𝗨𝗜` such that every well typed sentence `φ` that is true in `N` (with the
types ignored) is true in `M` when it is read along some strictly increasing sequence of levels
`ℓ`: a variable of type `t` ranges over the type `ℓ t` of `M`, and membership between the levels
`ℓ t` and `ℓ (t + 1)` is `SMem`. That reading is the typed formula `skip ℓ [] φ` of `M`. -/
theorem exists_nfui_model :
    ∃ (N : Type) (_ : SetStructure N) (_ : Nonempty N), N↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 ∧
      ∀ φ : TFm, TFm.Strat [] φ → TFm.Sat (fun a b : N => a ∈ b) φ [] →
        ∃ ℓ : ℕ → ℕ, StrictMono ℓ ∧ ∀ v : ℕ → M, Holds (skip ℓ [] φ) v := by
  let N := JensenNFU.Gen.V (Car M)
  let _ : SetStructure N := ⟨fun y x ↦ JensenNFU.Gen.memV x y⟩
  have h : JensenNFU.IsNFU N (fun a b : N ↦ a ∈ b) := JensenNFU.Gen.isNFU_V
  have hinf : JensenNFU.UnivInfinite (fun a b : N ↦ a ∈ b) := JensenNFU.Gen.inf_V
  have hne : Nonempty N := by
    obtain ⟨y, -⟩ := h.comprehension 0 [] (TFm.eq 0 0) ⟨0, rfl, rfl⟩ [] rfl
    exact ⟨y⟩
  refine ⟨N, inferInstance, hne, SetTheory.Jensen.models_nfui_of_isNFU h hinf, ?_⟩
  intro φ hφ hsat
  obtain ⟨ℓ, hℓ, hT⟩ := JensenNFU.Gen.exists_levels (C := Car M) φ hφ hsat
  obtain ⟨d⟩ := (JBase₀.ne : Nonempty (Car M))
  refine ⟨ℓ, hℓ, fun v => ?_⟩
  have h1 := (tsat_iff_satT d ℓ φ [] [] hφ rfl).mp hT
  have h2 := (holds_skip hℓ φ [] (fun i => ([] : List (Car M)).getD i d) hφ
    (by intro i hi; simp at hi)).mp h1
  exact (TFm.satT_congr (skip ℓ [] φ) [] _ v (strat_skip hℓ φ [] hφ)
    (by intro i hi; simp at hi)).mp h2

end TST

end FFL.FirstOrder
