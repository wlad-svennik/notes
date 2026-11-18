import NFInterpretsMH
import MHCond

set_option autoImplicit false

/-!
# `𝗠𝗛` interprets Mac Lane set theory with Choice

`𝗠𝗛` is Mathias's `𝗠` with the collapse axiom (`MHTheory`). Inside a model of `𝗠𝗛` the
constructible sets, the members of the levels `Lev γ`, with the same membership and equality,
form a model of `𝗠𝗔𝗖 = 𝗠 + 𝗔𝗖`.

* extensionality and foundation: the constructible sets form a transitive class;
* pairs and transitive containment: every level is a constructible transitive set;
* infinity: the level at `ω`;
* separation: `sep_good` (`MHSep`);
* power set: `bound_exists` (`MHCond`), which uses the collapse axiom;
* Choice: the eighth operation of the levels gives the order of a level as a constructible
  set, and the levels are well-ordered (`wol`, `MHOrder`).

* `mhInterpretsMAC : 𝗠𝗛 ⊳ 𝗠𝗔𝗖`.
* `nfInterpretsMAC : 𝗡𝗙 ⊳ 𝗠𝗔𝗖`, by composition with `nfInterpretsMH : 𝗡𝗙 ⊳ 𝗠𝗛`.
* `nfuInterpretsMAC : 𝗡𝗙𝗨𝗜 ⊳ 𝗠𝗔𝗖`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-! ### Evaluation along an isomorphism -/

section iso

variable {A B : Type} [SetStructure A] [SetStructure B] (j : A → B)

lemma val_iso {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) (e : Fin n → A) (ε : ℕ → A) :
    Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) t =
      j (Semiterm.val (M := A) e ε t) := by
  match t with
  | #x => simp
  | &x => simp
  | .func f _ => exact Empty.elim f

/-- **A bijection that preserves membership preserves the truth of formulas.** -/
theorem eval_iso (hinj : Function.Injective j) (hsurj : Function.Surjective j)
    (hmem : ∀ a a' : A, a ∈ a' ↔ j a ∈ j a') :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (e : Fin n → A) (ε : ℕ → A),
      Eval (M := A) e ε φ ↔ Eval (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) φ := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e ε; simp
  | hfalsum => intro e ε; simp
  | hrel r v =>
    intro e ε
    cases r with
    | eq =>
      show (Semiterm.val (M := A) e ε (v 0) = Semiterm.val (M := A) e ε (v 1)) ↔
        (Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 0) =
          Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 1))
      rw [val_iso, val_iso]
      exact ⟨fun h => congrArg j h, fun h => hinj h⟩
    | mem =>
      show (Semiterm.val (M := A) e ε (v 0) ∈ Semiterm.val (M := A) e ε (v 1)) ↔
        (Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 0) ∈
          Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 1))
      rw [val_iso, val_iso]
      exact hmem _ _
  | hnrel r v =>
    intro e ε
    cases r with
    | eq =>
      show ¬(Semiterm.val (M := A) e ε (v 0) = Semiterm.val (M := A) e ε (v 1)) ↔
        ¬(Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 0) =
          Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 1))
      rw [val_iso, val_iso]
      exact not_congr ⟨fun h => congrArg j h, fun h => hinj h⟩
    | mem =>
      show ¬(Semiterm.val (M := A) e ε (v 0) ∈ Semiterm.val (M := A) e ε (v 1)) ↔
        ¬(Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 0) ∈
          Semiterm.val (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (v 1))
      rw [val_iso, val_iso]
      exact not_congr (hmem _ _)
  | hand φ ψ ih1 ih2 =>
    intro e ε
    have h1 : Eval (M := A) e ε (φ ⋏ ψ) ↔ Eval (M := A) e ε φ ∧ Eval (M := A) e ε ψ := by simp
    have h2 : Eval (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (φ ⋏ ψ) ↔
        Eval (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) φ ∧
          Eval (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) ψ := by simp
    exact h1.trans ((and_congr (ih1 e ε) (ih2 e ε)).trans h2.symm)
  | hor φ ψ ih1 ih2 =>
    intro e ε
    have h1 : Eval (M := A) e ε (φ ⋎ ψ) ↔ Eval (M := A) e ε φ ∨ Eval (M := A) e ε ψ := by simp
    have h2 : Eval (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) (φ ⋎ ψ) ↔
        Eval (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) φ ∨
          Eval (M := B) (fun k ↦ j (e k)) (fun k ↦ j (ε k)) ψ := by simp
    exact h1.trans ((or_congr (ih1 e ε) (ih2 e ε)).trans h2.symm)
  | hall φ ih =>
    intro e ε
    have key : ∀ x : A, (fun k ↦ j ((x :> e) k)) = (j x :> fun k ↦ j (e k)) := by
      intro x; funext k; cases k using Fin.cases <;> simp
    simp only [eval_all]
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := hsurj y
      have := (ih (x :> e) ε).mp (h x)
      rwa [key] at this
    · intro h x
      refine (ih (x :> e) ε).mpr ?_
      rw [key]
      exact h (j x)
  | hexs φ ih =>
    intro e ε
    have key : ∀ x : A, (fun k ↦ j ((x :> e) k)) = (j x :> fun k ↦ j (e k)) := by
      intro x; funext k; cases k using Fin.cases <;> simp
    simp only [eval_ex]
    constructor
    · rintro ⟨x, h⟩
      have := (ih (x :> e) ε).mp h
      rw [key] at this
      exact ⟨j x, this⟩
    · rintro ⟨y, h⟩
      obtain ⟨x, rfl⟩ := hsurj y
      refine ⟨x, (ih (x :> e) ε).mpr ?_⟩
      rw [key]
      exact h

end iso

namespace MH

/-! ### The constructible sets -/

section con

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- `x` is constructible: a member of a level. -/
def Con (x : V) : Prop := ∃ γ : V, Ord γ ∧ x ∈ Lev γ

theorem con_tr {x y : V} (hx : Con x) (hy : y ∈ x) : Con y :=
  let ⟨γ, hγ, h⟩ := hx; ⟨γ, hγ, lev_tr hγ x h y hy⟩

theorem big_om : Big (om : V) := ⟨ord_om, fun _ h => h⟩

theorem con_big {x : V} (hx : Con x) : ∃ γ : V, Big γ ∧ x ∈ Lev γ := by
  obtain ⟨γ, hγ, h⟩ := hx
  rcases ord_tri hγ (ord_om (V := V)) with e | e | e
  · exact ⟨om, big_om, lev_mono ord_om e x h⟩
  · exact ⟨om, big_om, e ▸ h⟩
  · exact ⟨γ, ⟨hγ, fun n hn => hγ.1 om e n hn⟩, h⟩

theorem con_big2 {x y : V} (hx : Con x) (hy : Con y) :
    ∃ γ : V, Big γ ∧ x ∈ Lev γ ∧ y ∈ Lev γ := by
  obtain ⟨γ₁, g₁, h₁⟩ := con_big hx
  obtain ⟨γ₂, g₂, h₂⟩ := con_big hy
  rcases ord_tri g₁.1 g₂.1 with h | h | h
  · exact ⟨γ₂, g₂, lev_mono g₂.1 h x h₁, h₂⟩
  · exact ⟨γ₂, g₂, h ▸ h₁, h₂⟩
  · exact ⟨γ₁, g₁, h₁, lev_mono g₁.1 h y h₂⟩

theorem con_lev {γ : V} (hγ : Ord γ) : Con (Lev γ) :=
  ⟨sc γ, ord_sc hγ, lev_mem (ord_sc hγ) (self_mem_sc γ)⟩

theorem good_of_con {x : V} (hx : Con x) : Good (fun _ : V ↦ True) x :=
  let ⟨γ, hγ, h⟩ := con_big hx; ⟨trivial, γ, hγ, trivial, h⟩

theorem con_of_good {x : V} (hx : Good (fun _ : V ↦ True) x) : Con x :=
  let ⟨_, γ, hγ, _, h⟩ := hx; ⟨γ, hγ.1, h⟩

variable {W : Type} [SetStructure W] (i : W → V) (hi : Function.Injective i)
  (hran : ∀ x : V, Con x ↔ ∃ w, i w = x) (hmem : ∀ a b : W, a ∈ b ↔ i a ∈ i b)

include hi hran hmem

/-- **The constructible sets satisfy the conditions `IsMacBase`.** -/
theorem isMacBase_of_con : IsMacBase W := by
  have hcon : ∀ w, Con (i w) := fun w => (hran _).mpr ⟨w, rfl⟩
  have lift : ∀ {x : V} (w : W), x ∈ i w → ∃ w', i w' = x ∧ w' ∈ w := fun {x} w hx => by
    obtain ⟨w', hw'⟩ := (hran _).mp (con_tr (hcon w) hx)
    exact ⟨w', hw', (hmem _ _).mpr (by rw [hw']; exact hx)⟩
  refine ⟨fun x y h => ?_, fun x hx => ?_, fun x y => ?_, fun x => ?_, fun x => ?_, ?_,
    fun t ψ ε => ?_⟩
  · apply hi
    refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨w, hw, hwx⟩ := lift x hz
      rw [← hw]
      exact (hmem _ _).mp ((h w).mp hwx)
    · obtain ⟨w, hw, hwy⟩ := lift y hz
      rw [← hw]
      exact (hmem _ _).mp ((h w).mpr hwy)
  · obtain ⟨y, hy⟩ := hx
    obtain ⟨m, hm, hmin⟩ := m_found (i x) ⟨i y, (hmem _ _).mp hy⟩
    obtain ⟨w, hw, hwx⟩ := lift x hm
    refine ⟨w, hwx, fun z hz hzw => hmin (i z) ((hmem _ _).mp hz) ?_⟩
    rw [← hw]
    exact (hmem _ _).mp hzw
  · obtain ⟨γ, hγ, h1, h2⟩ := con_big2 (hcon x) (hcon y)
    obtain ⟨p, hp⟩ := (hran _).mp (con_lev hγ.1)
    exact ⟨p, (hmem _ _).mpr (by rw [hp]; exact h1), (hmem _ _).mpr (by rw [hp]; exact h2)⟩
  · obtain ⟨ν, hν, hx⟩ := con_big (hcon x)
    obtain ⟨κ, hκ, hb⟩ := bound_exists hν
    obtain ⟨p, hp⟩ := (hran _).mp (con_lev hκ)
    refine ⟨p, fun z hz => (hmem _ _).mpr ?_⟩
    rw [hp]
    obtain ⟨δ, hδ, hzδ⟩ := hcon z
    refine hb δ (i z) hδ hzδ fun u hu => ?_
    obtain ⟨w, hw, hwz⟩ := lift z hu
    rw [← hw]
    exact lev_tr hν.1 _ hx _ ((hmem _ _).mp (hz w hwz))
  · obtain ⟨γ, hγ, hx⟩ := hcon x
    obtain ⟨t, ht⟩ := (hran _).mp (con_lev hγ)
    refine ⟨t, fun z hz => (hmem _ _).mpr ?_, fun y hy z hz => (hmem _ _).mpr ?_⟩
    · rw [ht]
      exact lev_tr hγ _ hx _ ((hmem _ _).mp hz)
    · have hy' := (hmem _ _).mp hy
      rw [ht] at hy' ⊢
      exact lev_tr hγ _ hy' _ ((hmem _ _).mp hz)
  · obtain ⟨I, hI⟩ := (hran _).mp (con_lev (ord_om (V := V)))
    obtain ⟨e, he⟩ := (hran (∅ : V)).mp ⟨nm 1, ord_nm 1, nm_mem_lev_nm 0⟩
    refine ⟨I, ⟨e, (hmem _ _).mpr ?_, fun z hz => ?_⟩, fun x hx => ?_⟩
    · rw [hI, he]
      exact nm_mem_lev big_om 0
    · have := (hmem _ _).mp hz
      rw [he] at this
      exact absurd this (by simp)
    · have hx' : i x ∈ Lev (om : V) := by
        have := (hmem _ _).mp hx
        rwa [hI] at this
      obtain ⟨β, hβ, hin⟩ := (mem_lev ord_om).mp hx'
      have hβO := ord_mem ord_om hβ
      have h1 : i x ∈ Lev (sc β) := inDef_mem hβO hin
      have h2 : (insert (i x) (i x) : V) ∈ Lev (sc (sc β)) :=
        adj_mem_lev (ord_sc hβO) ⟨β, self_mem_sc β⟩ h1 h1
      have h3 : (insert (i x) (i x) : V) ∈ Lev (om : V) :=
        lev_mono ord_om (sc_mem_om (sc_mem_om hβ)) _ h2
      obtain ⟨x', hx'e⟩ := (hran _).mp ⟨om, ord_om, h3⟩
      refine ⟨x', (hmem _ _).mpr (by rw [hI, hx'e]; exact h3), fun z => ?_⟩
      rw [hmem, hx'e]
      constructor
      · intro h
        rcases (by simpa using h : i z = i x ∨ i z ∈ i x) with e | e
        · exact Or.inl (hi e)
        · exact Or.inr ((hmem _ _).mpr e)
      · rintro (e | e)
        · rw [e]; simp
        · have := (hmem _ _).mp e
          simp [this]
  · have ht := good_of_con (hcon t)
    let ε' : ℕ → extSet (i t) := fun k => ⟨i (ε k), (hmem _ _).mp (ε k).2⟩
    obtain ⟨Y, hY, hYm⟩ := sep_good closed_true ht ψ ε' (fun k => good_of_con (hcon (ε k)))
    obtain ⟨y, hy⟩ := (hran _).mp (con_of_good hY)
    let j : extSet t → extSet (i t) := fun a => ⟨i a, (hmem _ _).mp a.2⟩
    have hj1 : Function.Injective j := fun a b h => Subtype.ext (hi (congrArg Subtype.val h))
    have hj2 : Function.Surjective j := fun b => by
      obtain ⟨w, hw, hwt⟩ := lift t b.2
      exact ⟨⟨w, hwt⟩, Subtype.ext hw⟩
    have hj3 : ∀ a a' : extSet t, a ∈ a' ↔ j a ∈ j a' := fun a a' => hmem _ _
    have hvec : ∀ a : extSet t, (fun k ↦ j ((![a] : Fin 1 → extSet t) k)) = ![j a] := by
      intro a
      funext k
      have : k = 0 := Subsingleton.elim _ _
      subst this
      rfl
    refine ⟨y, fun z => ?_⟩
    rw [hmem, hy, hYm]
    constructor
    · rintro ⟨hz, hev⟩
      have hz' : z ∈ extSet t := (hmem _ _).mpr hz
      refine ⟨hz', (eval_iso j hj1 hj2 hj3 ψ ![⟨z, hz'⟩] ε).mpr ?_⟩
      rw [hvec]
      exact hev
    · rintro ⟨hz, hev⟩
      have hz' : i z ∈ extSet (i t) := (hmem _ _).mp hz
      refine ⟨hz', ?_⟩
      have := (eval_iso j hj1 hj2 hj3 ψ ![⟨z, hz⟩] ε).mp hev
      rw [hvec] at this
      exact this

/-- **The constructible sets satisfy the axiom of choice**: a family of pairwise disjoint sets
with members has a choice set. -/
theorem ac_of_con : ∀ 𝓧 : W, (∀ X ∈ 𝓧, ∃ y, y ∈ X) →
    (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) → ∃ C : W, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X := by
  intro 𝓧 hne hdis
  have hcon : ∀ w, Con (i w) := fun w => (hran _).mpr ⟨w, rfl⟩
  have lift : ∀ {x : V} (w : W), x ∈ i w → ∃ w', i w' = x ∧ w' ∈ w := fun {x} w hx => by
    obtain ⟨w', hw'⟩ := (hran _).mp (con_tr (hcon w) hx)
    exact ⟨w', hw', (hmem _ _).mpr (by rw [hw']; exact hx)⟩
  obtain ⟨γ, hγ, hXγ⟩ := con_big (hcon 𝓧)
  have g₃ : Big (scn 4 γ) := big_scn hγ 4
  -- the order of a later level, as a constructible set
  obtain ⟨R, hR⟩ := exists_isD (Lev (scn 4 γ)) (LtS (scn 4 γ)) (nm 7) (∅ : V) ∅ ∅
  have hRm : ∀ z, z ∈ R ↔ z ∈ Lev (scn 4 γ) ∧ z ∈ LtS (scn 4 γ) := fun z =>
    ⟨fun h => ⟨(hR.1 z h).1, phi7.mp (hR.1 z h).2⟩, fun h => hR.2 z h.1 (phi7.mpr h.2)⟩
  have h0 : (∅ : V) ∈ Lev (scn 4 γ) := nm_mem_lev g₃ 0
  have hRL : R ∈ Lev (sc (scn 4 γ)) :=
    def_mem_lev (ord_sc g₃.1) (self_mem_sc _) (nm_mem_lev g₃ 7) h0 h0 h0 hR
  have hRlt : ∀ a b, a ∈ Lev γ → b ∈ Lev γ → (Pr R a b ↔ LtL a b) := by
    intro a b ha hb
    have ha₃ := lev_scn_sub hγ.1 4 a ha
    have hb₃ := lev_scn_sub hγ.1 4 b hb
    rw [pr_iff, hRm]
    constructor
    · rintro ⟨-, h⟩
      exact ((lts_iff g₃.1).mp (pr_iff.mpr h)).2.2
    · intro h
      exact ⟨kp_mem_lev hγ ha hb, pr_iff.mp ((lts_iff g₃.1).mpr ⟨ha₃, hb₃, h⟩)⟩
  have g₅ : Big (sc (scn 4 γ)) := big_sc g₃
  have hup : ∀ z, z ∈ Lev γ → z ∈ Lev (sc (scn 4 γ)) := fun z hz =>
    lev_mono g₅.1 (self_mem_sc _) _ (lev_scn_sub hγ.1 4 _ hz)
  have hgood : Good (fun _ : V ↦ True) (Lev (sc (scn 4 γ))) := good_of_con (con_lev g₅.1)
  have hp : ∀ k : Fin 2, (![i 𝓧, R] : Fin 2 → V) k ∈ Lev (sc (scn 4 γ)) ∧
      Good (fun _ : V ↦ True) ((![i 𝓧, R] : Fin 2 → V) k) := by
    intro k
    match k with
    | 0 => exact ⟨hup _ hXγ, good_of_con (hcon 𝓧)⟩
    | 1 => exact ⟨hRL, good_of_con ⟨_, g₅.1, hRL⟩⟩
  obtain ⟨Cv, hCg, hCm⟩ := sep_good_bdef closed_true (k := 2)
    (BDef.bex 1 ((BDef.mem 1 0).and (BDef.ball 0 (prB.comp ![4, 0, 2]).not))) hgood
    (lev_tr g₅.1) ![i 𝓧, R] hp
  have hCm' : ∀ z, z ∈ Cv ↔ z ∈ Lev (sc (scn 4 γ)) ∧
      ∃ X, X ∈ i 𝓧 ∧ (z ∈ X ∧ ∀ w, w ∈ X → ¬Pr R w z) := fun z => hCm z
  obtain ⟨C, hC⟩ := (hran _).mp (con_of_good hCg)
  refine ⟨C, fun X hX => ?_⟩
  have hXv : i X ∈ i 𝓧 := (hmem _ _).mp hX
  have hXsub : ∀ z, z ∈ i X → z ∈ Lev γ := fun z hz =>
    lev_tr hγ.1 _ (lev_tr hγ.1 _ hXγ _ hXv) z hz
  obtain ⟨y, hy⟩ := hne X hX
  obtain ⟨m, hm, hmin⟩ := ltL_least hγ.1 (i X) hXsub ⟨i y, (hmem _ _).mp hy⟩
  obtain ⟨m', hm', hm'X⟩ := lift X hm
  have hmC : m ∈ Cv := (hCm' m).mpr ⟨hup m (hXsub m hm), i X, hXv, hm,
    fun w hw hp' => hmin w hw ((hRlt w m (hXsub w hw) (hXsub m hm)).mp hp')⟩
  refine ⟨m', ⟨(hmem _ _).mpr (by rw [hC, hm']; exact hmC), hm'X⟩, ?_⟩
  rintro x' ⟨hx'C, hx'X⟩
  have hxv : i x' ∈ Cv := by
    have := (hmem _ _).mp hx'C
    rwa [hC] at this
  obtain ⟨-, X₂, hX₂, hxX₂, hmin₂⟩ := (hCm' _).mp hxv
  obtain ⟨X₂', hX₂', hX₂'m⟩ := lift 𝓧 hX₂
  have hxX₂' : x' ∈ X₂' := (hmem _ _).mpr (by rw [hX₂']; exact hxX₂)
  have e : X₂' = X := hdis X₂' hX₂'m X hX ⟨x', hxX₂', hx'X⟩
  have hxXv : i x' ∈ i X := (hmem _ _).mp hx'X
  apply hi
  rw [hm']
  rcases ltL_tri hγ.1 (hXsub _ hxXv) (hXsub m hm) with h | h | h
  · exact absurd h (hmin _ hxXv)
  · exact h
  · exfalso
    have hmX₂ : m ∈ X₂ := by
      rw [← hX₂', e]
      exact hm
    exact hmin₂ m hmX₂ ((hRlt m (i x') (hXsub m hm) (hXsub _ hxXv)).mpr h)

end con

/-! ### The definition of the constructible sets by a formula -/

/-- `v 0` is a member of the last level of a sequence of levels. -/
def ConR : MRel 1 := fun V _ v ↦ ∃ δ D F A : V,
  Ord δ ∧ (SuccR D δ ∧ (IsAtt (k := 0) GMainR ![] F D ∧ (LevAt F δ A ∧ v 0 ∈ A)))

/-- The formula that defines the constructible sets. -/
def conF : FDef ConR :=
  (FDef.ex (FDef.ex (FDef.ex (FDef.ex ((ordB.toFDef.comp ![3]).and
    ((succB.toFDef.comp ![2, 3]).and (((isAttB gMainB).toFDef.comp ![1, 2]).and
      ((levAtB.toFDef.comp ![1, 3, 0]).and (BDef.mem 4 0).toFDef)))))))).congr
    fun V _ v => by
      refine exists_congr fun δ => exists_congr fun D => exists_congr fun F =>
        exists_congr fun A => and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
      have key : ∀ p q : Fin 0 → V,
          IsAtt (k := 0) GMainR p F D ↔ IsAtt (k := 0) GMainR q F D := fun p q => by
        rw [Subsingleton.elim p q]
      exact key _ _

section conf

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem conR_iff {x : V} : ConR V ![x] ↔ Con x := by
  constructor
  · rintro ⟨δ, D, F, A, hδ, hs, hatt, hlev, hx⟩
    have e : D = sc δ := succR_iff_sc.mp hs
    rw [e] at hatt
    have hF : IsHier F δ := hatt
    have e' := (levAt_lev hδ hF (self_mem_sc δ)).mp hlev
    exact ⟨δ, hδ, e' ▸ hx⟩
  · rintro ⟨γ, hγ, hx⟩
    obtain ⟨F, hF⟩ := exists_hier hγ
    exact ⟨γ, sc γ, F, Lev γ, hγ, succR_iff_sc.mpr rfl, hF,
      (levAt_lev hγ hF (self_mem_sc γ)).mpr rfl, hx⟩

end conf

end MH

/-! ### The interpretation -/

open DirectTranslation

/-- The interpretation of the relation symbols: equality and membership are themselves. -/
def lRel : {k : ℕ} → (ℒₛₑₜ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.Set.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.Set.Rel.mem => Semiformula.Operator.Mem.mem

section

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

lemma lDomain_val_iff (x : M) :
    (⟨MH.conF.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] ↔ MH.Con x :=
  (MH.conF.eval M ![x]).trans MH.conR_iff

end

/-- **The translation of `ℒₛₑₜ` into `𝗠𝗛`**: the domain is the constructible sets, and
membership and equality are themselves. -/
def lTranslation : DirectTranslation 𝗠𝗛 ℒₛₑₜ where
  domain := ⟨MH.conF.φ⟩
  rel := lRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    suffices ∃ x : M, (⟨MH.conF.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨∅, (lDomain_val_iff ∅).mpr ⟨MH.nm 1, MH.ord_nm 1, MH.nm_mem_lev_nm 0⟩⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : lRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

/-- A structure in which every family of pairwise disjoint sets with members has a choice set
is a model of `𝗔𝗖`, when it is given with its relation symbols. -/
theorem ac_models' {W : Type} [SetStructure W] [Nonempty W] [s : Tarski.Structure ℒₛₑₜ W]
    [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (h : ∀ 𝓧 : W, (∀ X ∈ 𝓧, ∃ y, y ∈ X) → (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) →
      ∃ C : W, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X) : W↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := by
  rcases standardStructure_unique W s
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ
  suffices ∀ 𝓧 : W, (∀ X ∈ 𝓧, IsNonempty X) →
      (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) → ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X by
    simpa [models_iff, Axiom.choice]
  intro 𝓧 hne hdis
  exact h 𝓧 (fun X hX => isNonempty_def.mp (hne X hX)) hdis

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The membership relation of the interpreted structure. -/
instance lModel_setStructure : SetStructure (lTranslation.Model M) :=
  ⟨fun y x ↦ (x : M) ∈ (y : M)⟩

omit [Nonempty M] hT in
lemma lModel_mem_iff (a b : lTranslation.Model M) : a ∈ b ↔ (a : M) ∈ (b : M) := Iff.rfl

instance lModel_mem : Tarski.Structure.Mem ℒₛₑₜ (lTranslation.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : lTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact Tarski.Structure.Mem.mem (L := ℒₛₑₜ) (a : M) (b : M)

/-- **In a model of `𝗠𝗛`, the constructible sets form a model of `𝗠𝗔𝗖`.** -/
theorem lModel_models : (lTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗔𝗖 := by
  have hinj : Function.Injective (fun a : lTranslation.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hran : ∀ x : M, MH.Con x ↔ ∃ w : lTranslation.Model M, (w : M) = x :=
    fun x => ⟨fun hx => ⟨⟨x, (lDomain_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (lDomain_val_iff _).mp w.dom⟩
  haveI h1 : (lTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗠 :=
    IsMacBase.models' (MH.isMacBase_of_con _ hinj hran lModel_mem_iff)
  haveI h2 : (lTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗔𝗖 :=
    ac_models' (MH.ac_of_con _ hinj hran lModel_mem_iff)
  exact inferInstance

end model

/-- **`𝗠𝗛` interprets Mac Lane set theory with Choice.** The domain is the constructible sets;
membership and equality are unchanged. -/
instance mhInterpretsMAC : 𝗠𝗛 ⊳ 𝗠𝗔𝗖 where
  trln := lTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp lModel_models φ hφ)

/-- **`𝗡𝗙` interprets Mac Lane set theory with Choice**, through `𝗠𝗛`. -/
instance nfInterpretsMAC : 𝗡𝗙 ⊳ 𝗠𝗔𝗖 := DirectInterpretation.comp mhInterpretsMAC nfInterpretsMH

/-- **NFU + Infinity interprets Mac Lane set theory with Choice**, through `𝗡𝗙` and `𝗠𝗛`. -/
instance nfuInterpretsMAC : 𝗡𝗙𝗨𝗜 ⊳ 𝗠𝗔𝗖 := DirectInterpretation.comp nfInterpretsMAC nfuInterpretsNF

/-- **The syntactic transformation.** The translation of a theorem of `𝗠𝗔𝗖` is a theorem of
`𝗡𝗙`. -/
theorem nf_provable_translate_of_mac {σ : Sentence ℒₛₑₜ} (h : 𝗠𝗔𝗖 ⊢ σ) :
    𝗡𝗙 ⊢ nfInterpretsMAC σ :=
  DirectInterpretation.sound nfInterpretsMAC h

/-- If `𝗡𝗙` is consistent then so is `𝗠𝗔𝗖`. -/
theorem consistent_mac_of_consistent_nf (h : Entailment.Consistent 𝗡𝗙) :
    Entailment.Consistent 𝗠𝗔𝗖 := by
  by_contra hM
  have hbot : 𝗠𝗔𝗖 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hM ⊥
  have := nf_provable_translate_of_mac hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If `𝗠𝗛` is consistent then so is `𝗠𝗔𝗖`. -/
theorem consistent_mac_of_consistent_mh (h : Entailment.Consistent 𝗠𝗛) :
    Entailment.Consistent 𝗠𝗔𝗖 := by
  by_contra hM
  have hbot : 𝗠𝗔𝗖 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hM ⊥
  have := DirectInterpretation.sound mhInterpretsMAC hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.mhInterpretsMAC
#print axioms FFL.FirstOrder.SetTheory.nfInterpretsMAC
#print axioms FFL.FirstOrder.SetTheory.nfuInterpretsMAC
#print axioms FFL.FirstOrder.SetTheory.consistent_mac_of_consistent_nf
