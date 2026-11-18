import ConNF.NF.NFUHartogs
import ConNF.NF.Hailperin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false



/-!
# Specker's theorem, part 1: injections between sets in a model of NF

A model of NF is a model of NFU in which every object is a set (`hS`). This file contains the
preorder `x ≼ y` ("there is an injection from `x` into `y`", the injection being a set of
Kuratowski pairs), its behaviour under singleton images and power sets, and Cantor's theorem.
Nothing here uses Infinity.
-/

namespace NFUCut

/-- A stratification given by a list. The names `100 + 3k`, `101 + 3k`, `102 + 3k` are
reserved for the auxiliary variables of the formulas below and have the types `k + 2`, `k + 1`,
`k`. -/
def σSp (l : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  if 100 ≤ i then (i - 100) / 3 + 2 - (i - 100) % 3 else (l.lookup i).getD 0

namespace Model

/-- `p = ⟨a, b⟩`, for `a`, `b` of type `k`. -/
def fP (k p a b : ℕ) : Fml := fOp p a b (101 + 3 * k) (102 + 3 * k)

/-- `⟨a, b⟩ ∈ f`, for `a`, `b` of type `k`. -/
def fI (k a b f : ℕ) : Fml :=
  Fml.ex (100 + 3 * k)
    (.and (fOp (100 + 3 * k) a b (101 + 3 * k) (102 + 3 * k)) (.mem (100 + 3 * k) f))

/-- `u = {a}`, for `a` of type `k`. -/
def fS (k u a : ℕ) : Fml := fSing u a (102 + 3 * k)

variable {V : Type} [Nonempty V] (M : Model V)

theorem sat_fP (k : ℕ) {p a b : ℕ} (hp : p < 100) (ha : a < 100) (hb : b < 100) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fP k p a b) ρ ↔ ρ p = M.op (ρ a) (ρ b) :=
  M.sat_fOp (p := p) (a := a) (b := b) (u := 101 + 3 * k) (c := 102 + 3 * k) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) ρ

theorem sat_fI (k : ℕ) {a b f : ℕ} (ha : a < 100) (hb : b < 100) (hf : f < 100) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fI k a b f) ρ ↔ M.mem (M.op (ρ a) (ρ b)) (ρ f) := by
  have h1 : a ≠ 100 + 3 * k := by omega
  have h2 : b ≠ 100 + 3 * k := by omega
  have h3 : f ≠ 100 + 3 * k := by omega
  simp only [fI, M.sat_ex, Sat, M.sat_fOp (p := 100 + 3 * k) (a := a) (b := b)
    (u := 101 + 3 * k) (c := 102 + 3 * k) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega), Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]
  exact ⟨fun ⟨q, hq, h⟩ => hq ▸ h, fun h => ⟨_, rfl, h⟩⟩

theorem sat_fS (k : ℕ) {u a : ℕ} (hu : u < 100) (ha : a < 100) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fS k u a) ρ ↔ ρ u = M.sing (ρ a) :=
  M.sat_fSing (u := u) (a := a) (c := 102 + 3 * k) (by omega) (by omega) ρ

/-! ## Injections -/

/-- `f` is an injection from `x` into `y`: every member of `x` is related by `f` to a member of
`y`, and on `x` the relation `f` is single-valued and one-to-one. Nothing is required of `f`
outside `x`. -/
def Inj (f x y : V) : Prop :=
  (∀ u, M.mem u x → ∃ w, M.mem w y ∧ M.mem (M.op u w) f) ∧
    ∀ u u' w w', M.mem u x → M.mem u' x → M.mem (M.op u w) f → M.mem (M.op u' w') f →
      (u = u' ↔ w = w')

/-- `x ≼ y`: there is an injection from `x` into `y`. -/
def Le (x y : V) : Prop := ∃ f, M.Inj f x y

/-- `x ≈ y`: each of `x`, `y` injects into the other. -/
def Eqv (x y : V) : Prop := M.Le x y ∧ M.Le y x

theorem exists_idRel : ∃ I, ∀ p, M.mem p I ↔ ∃ u, p = M.op u u := by
  obtain ⟨I, -, h⟩ := M.comp (σSp [(0, 2)]) (Fml.ex 1 (fP 0 0 1 1)) 0 rfl (fun _ => dflt)
  refine ⟨I, fun p => ?_⟩
  rw [h p]
  simp [M.sat_ex, M.sat_fP, Function.update_apply]

theorem le_of_sub {x y : V} (h : ∀ a, M.mem a x → M.mem a y) : M.Le x y := by
  obtain ⟨I, hI⟩ := M.exists_idRel
  refine ⟨I, fun u hu => ⟨u, h u hu, (hI _).mpr ⟨u, rfl⟩⟩, fun u u' w w' _ _ h1 h2 => ?_⟩
  obtain ⟨v, hv⟩ := (hI _).mp h1
  obtain ⟨v', hv'⟩ := (hI _).mp h2
  obtain ⟨e1, e2⟩ := M.op_inj hv
  obtain ⟨e3, e4⟩ := M.op_inj hv'
  rw [e1, e2, e3, e4]

theorem le_rfl' (x : V) : M.Le x x := M.le_of_sub fun _ h => h

theorem le_trans' {x y z : V} (h1 : M.Le x y) (h2 : M.Le y z) : M.Le x z := by
  obtain ⟨f, hf1, hf2⟩ := h1
  obtain ⟨g, hg1, hg2⟩ := h2
  obtain ⟨h, -, hh⟩ := M.comp (σSp [(0, 2), (1, 3), (2, 3), (3, 1)])
    (Fml.ex 4 (Fml.ex 5 (Fml.ex 6 (.and (fP 0 0 4 6) (.and (.mem 5 3)
      (.and (fI 0 4 5 1) (fI 0 5 6 2)))))))
    0 rfl (Function.update (Function.update (Function.update (fun _ => dflt) 1 f) 2 g) 3 y)
  have hh' : ∀ p, M.mem p h ↔ ∃ u w v, p = M.op u v ∧ M.mem w y ∧ M.mem (M.op u w) f ∧
      M.mem (M.op w v) g := by
    intro p
    rw [hh p]
    simp [M.sat_ex, Sat, M.sat_fP, M.sat_fI, Function.update_apply]
  refine ⟨h, fun u hu => ?_, fun u u' v v' hu hu' hp hp' => ?_⟩
  · obtain ⟨w, hw, hfw⟩ := hf1 u hu
    obtain ⟨v, hv, hgv⟩ := hg1 w hw
    exact ⟨v, hv, (hh' _).mpr ⟨u, w, v, rfl, hw, hfw, hgv⟩⟩
  · obtain ⟨u1, w, v1, e, hw, hfw, hgv⟩ := (hh' _).mp hp
    obtain ⟨u1', w', v1', e', hw', hfw', hgv'⟩ := (hh' _).mp hp'
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨e3, e4⟩ := M.op_inj e'
    subst e1 e2 e3 e4
    exact (hf2 u u' w w' hu hu' hfw hfw').trans (hg2 w w' v v' hw hw' hgv hgv')

theorem eqv_rfl (x : V) : M.Eqv x x := ⟨M.le_rfl' x, M.le_rfl' x⟩

theorem eqv_symm {x y : V} (h : M.Eqv x y) : M.Eqv y x := ⟨h.2, h.1⟩

theorem eqv_trans {x y z : V} (h1 : M.Eqv x y) (h2 : M.Eqv y z) : M.Eqv x z :=
  ⟨M.le_trans' h1.1 h2.1, M.le_trans' h2.2 h1.2⟩

/-- The converse of an injection that is onto. -/
theorem le_conv {f x y : V} (hf : M.Inj f x y)
    (hsurj : ∀ w, M.mem w y → ∃ u, M.mem u x ∧ M.mem (M.op u w) f) : M.Le y x := by
  obtain ⟨g, -, hg⟩ := M.comp (σSp [(0, 2), (1, 3), (2, 1), (3, 1)])
    (Fml.ex 4 (Fml.ex 5 (.and (fP 0 0 5 4) (.and (.mem 4 2) (.and (.mem 5 3) (fI 0 4 5 1))))))
    0 rfl (Function.update (Function.update (Function.update (fun _ => dflt) 1 f) 2 x) 3 y)
  have hg' : ∀ p, M.mem p g ↔ ∃ u w, p = M.op w u ∧ M.mem u x ∧ M.mem w y ∧
      M.mem (M.op u w) f := by
    intro p
    rw [hg p]
    simp [M.sat_ex, Sat, M.sat_fP, M.sat_fI, Function.update_apply]
  refine ⟨g, fun w hw => ?_, fun w w' u u' hw hw' hp hp' => ?_⟩
  · obtain ⟨u, hu, hfu⟩ := hsurj w hw
    exact ⟨u, hu, (hg' _).mpr ⟨u, w, rfl, hu, hw, hfu⟩⟩
  · obtain ⟨u1, w1, e, hu1, hw1, hf1⟩ := (hg' _).mp hp
    obtain ⟨u1', w1', e', hu1', hw1', hf1'⟩ := (hg' _).mp hp'
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨e3, e4⟩ := M.op_inj e'
    subst e1 e2 e3 e4
    exact (hf.2 u u' w w' hu1 hu1' hf1 hf1').symm

/-- The image of `x` under an injection is equivalent to `x`. -/
theorem inj_img {f x y : V} (hf : M.Inj f x y) :
    (∀ s, M.mem s (M.img f x) → M.mem s y) ∧ M.Le x (M.img f x) ∧ M.Le (M.img f x) x := by
  have hsub : ∀ s, M.mem s (M.img f x) → M.mem s y := by
    intro s hs
    obtain ⟨a, ha, hp⟩ := M.mem_img.mp hs
    obtain ⟨w, hw, hpw⟩ := hf.1 a ha
    have e := (hf.2 a a s w ha ha hp hpw).mp rfl
    rw [e]
    exact hw
  have hinj : M.Inj f x (M.img f x) :=
    ⟨fun u hu => by
      obtain ⟨w, hw, hp⟩ := hf.1 u hu
      exact ⟨w, M.mem_img.mpr ⟨u, hu, hp⟩, hp⟩, hf.2⟩
  exact ⟨hsub, ⟨f, hinj⟩, M.le_conv hinj fun w hw => M.mem_img.mp hw⟩

/-! ## Singleton images -/

theorem le_simg {x y : V} (h : M.Le x y) : M.Le (M.simg x) (M.simg y) := by
  obtain ⟨f, hf1, hf2⟩ := h
  obtain ⟨g, -, hg⟩ := M.comp (σSp [(0, 3), (1, 3), (6, 1), (7, 1)])
    (Fml.ex 4 (Fml.ex 5 (Fml.ex 6 (Fml.ex 7 (.and (fP 1 0 6 7) (.and (fS 0 6 4)
      (.and (fS 0 7 5) (fI 0 4 5 1))))))))
    0 rfl (Function.update (fun _ => dflt) 1 f)
  have hg' : ∀ p, M.mem p g ↔ ∃ u w, p = M.op (M.sing u) (M.sing w) ∧ M.mem (M.op u w) f := by
    intro p
    rw [hg p]
    simp [M.sat_ex, Sat, M.sat_fP, M.sat_fS, M.sat_fI, Function.update_apply]
  refine ⟨g, fun s hs => ?_, fun s s' t t' hs hs' hp hp' => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := M.mem_simg.mp hs
    obtain ⟨w, hw, hfw⟩ := hf1 u hu
    exact ⟨M.sing w, M.mem_simg.mpr ⟨w, hw, rfl⟩, (hg' _).mpr ⟨u, w, rfl, hfw⟩⟩
  · obtain ⟨u, hu, rfl⟩ := M.mem_simg.mp hs
    obtain ⟨u', hu', rfl⟩ := M.mem_simg.mp hs'
    obtain ⟨u1, w1, e, hf⟩ := (hg' _).mp hp
    obtain ⟨u1', w1', e', hf'⟩ := (hg' _).mp hp'
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨e3, e4⟩ := M.op_inj e'
    have e1' := M.sing_inj e1
    have e3' := M.sing_inj e3
    subst e1' e3' e2 e4
    have key := hf2 u u' w1 w1' hu hu' hf hf'
    exact ⟨fun h => congrArg M.sing (key.mp (M.sing_inj h)),
      fun h => congrArg M.sing (key.mpr (M.sing_inj h))⟩

theorem le_of_simg {x y : V} (h : M.Le (M.simg x) (M.simg y)) : M.Le x y := by
  obtain ⟨f, hf1, hf2⟩ := h
  obtain ⟨g, -, hg⟩ := M.comp (σSp [(0, 2), (1, 4), (6, 1), (7, 1)])
    (Fml.ex 4 (Fml.ex 5 (Fml.ex 6 (Fml.ex 7 (.and (fP 0 0 4 5) (.and (fS 0 6 4)
      (.and (fS 0 7 5) (fI 1 6 7 1))))))))
    0 rfl (Function.update (fun _ => dflt) 1 f)
  have hg' : ∀ p, M.mem p g ↔ ∃ u w, p = M.op u w ∧ M.mem (M.op (M.sing u) (M.sing w)) f := by
    intro p
    rw [hg p]
    simp [M.sat_ex, Sat, M.sat_fP, M.sat_fS, M.sat_fI, Function.update_apply]
  refine ⟨g, fun u hu => ?_, fun u u' w w' hu hu' hp hp' => ?_⟩
  · obtain ⟨t, ht, hft⟩ := hf1 (M.sing u) (M.mem_simg.mpr ⟨u, hu, rfl⟩)
    obtain ⟨w, hw, rfl⟩ := M.mem_simg.mp ht
    exact ⟨w, hw, (hg' _).mpr ⟨u, w, rfl, hft⟩⟩
  · obtain ⟨u1, w1, e, hf⟩ := (hg' _).mp hp
    obtain ⟨u1', w1', e', hf'⟩ := (hg' _).mp hp'
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨e3, e4⟩ := M.op_inj e'
    subst e1 e2 e3 e4
    have key := hf2 (M.sing u) (M.sing u') (M.sing w) (M.sing w')
      (M.mem_simg.mpr ⟨u, hu, rfl⟩) (M.mem_simg.mpr ⟨u', hu', rfl⟩) hf hf'
    exact ⟨fun h => M.sing_inj (key.mp (congrArg M.sing h)),
      fun h => M.sing_inj (key.mpr (congrArg M.sing h))⟩

theorem eqv_simg {x y : V} (h : M.Eqv x y) : M.Eqv (M.simg x) (M.simg y) :=
  ⟨M.le_simg h.1, M.le_simg h.2⟩

theorem eqv_of_simg {x y : V} (h : M.Eqv (M.simg x) (M.simg y)) : M.Eqv x y :=
  ⟨M.le_of_simg h.1, M.le_of_simg h.2⟩

/-! ## Power sets -/

section nf

variable (hS : ∀ x : V, M.isSet x)
include hS

theorem mem_pow' {x y : V} : M.mem y (M.pow x) ↔ ∀ z, M.mem z y → M.mem z x :=
  M.mem_pow.trans ⟨fun h => h.2, fun h => ⟨hS y, h⟩⟩

theorem ext' {x y : V} (h : ∀ z, M.mem z x ↔ M.mem z y) : x = y := M.ext (hS x) (hS y) h

theorem pow_univ : M.pow M.univ = M.univ :=
  M.ext' hS fun z => ⟨fun _ => M.mem_univ z, fun _ => (M.mem_pow' hS).mpr fun w _ => M.mem_univ w⟩

theorem simg_inj {s s' : V} (h : M.simg s = M.simg s') : s = s' := by
  refine M.ext' hS fun u => ?_
  constructor
  · intro hu
    have : M.mem (M.sing u) (M.simg s') := h ▸ M.mem_simg.mpr ⟨u, hu, rfl⟩
    obtain ⟨a, ha, e⟩ := M.mem_simg.mp this
    rw [M.sing_inj e]
    exact ha
  · intro hu
    have : M.mem (M.sing u) (M.simg s) := h ▸ M.mem_simg.mpr ⟨u, hu, rfl⟩
    obtain ⟨a, ha, e⟩ := M.mem_simg.mp this
    rw [M.sing_inj e]
    exact ha

/-- A set of singletons is the singleton image of its union. -/
theorem simg_sUnion {t : V} (ht : ∀ e, M.mem e t → ∃ d, e = M.sing d) :
    M.simg (M.sUnion t) = t := by
  refine M.ext' hS fun e => ?_
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := M.mem_simg.mp he
    obtain ⟨z, hz, hdz⟩ := M.mem_sUnion.mp hd
    obtain ⟨d', rfl⟩ := ht z hz
    rw [M.mem_sing.mp hdz]
    exact hz
  · intro he
    obtain ⟨d, rfl⟩ := ht e he
    exact M.mem_simg.mpr ⟨d, M.mem_sUnion.mpr ⟨_, he, M.mem_sing.mpr rfl⟩, rfl⟩

theorem le_pow {x y : V} (h : M.Le x y) : M.Le (M.pow x) (M.pow y) := by
  obtain ⟨f, hf1, hf2⟩ := h
  obtain ⟨g, -, hg⟩ := M.comp (σSp [(0, 3), (1, 3), (4, 1), (5, 1)])
    (Fml.ex 4 (Fml.ex 5 (.and (fP 1 0 4 5)
      (.all 6 (Fml.iff (.mem 6 5) (Fml.ex 7 (.and (.mem 7 4) (fI 0 7 6 1))))))))
    0 rfl (Function.update (fun _ => dflt) 1 f)
  have hg' : ∀ p, M.mem p g ↔ ∃ s t, p = M.op s t ∧
      ∀ w, M.mem w t ↔ ∃ u, M.mem u s ∧ M.mem (M.op u w) f := by
    intro p
    rw [hg p]
    simp [M.sat_ex, Sat, M.sat_iff, M.sat_fP, M.sat_fI, Function.update_apply]
  refine ⟨g, fun s hs => ?_, fun s s' t t' hs hs' hp hp' => ?_⟩
  · have hs' := (M.mem_pow' hS).mp hs
    refine ⟨M.img f s, (M.mem_pow' hS).mpr fun w hw => ?_, (hg' _).mpr ⟨s, _, rfl, fun w => M.mem_img⟩⟩
    obtain ⟨u, hu, hfu⟩ := M.mem_img.mp hw
    obtain ⟨w', hw', hfw'⟩ := hf1 u (hs' u hu)
    rw [(hf2 u u w w' (hs' u hu) (hs' u hu) hfu hfw').mp rfl]
    exact hw'
  · have hsx := (M.mem_pow' hS).mp hs
    have hsx' := (M.mem_pow' hS).mp hs'
    obtain ⟨s1, t1, e, ht⟩ := (hg' _).mp hp
    obtain ⟨s1', t1', e', ht'⟩ := (hg' _).mp hp'
    obtain ⟨e1, e2⟩ := M.op_inj e
    obtain ⟨e3, e4⟩ := M.op_inj e'
    subst e1 e2 e3 e4
    constructor
    · intro h
      subst h
      exact M.ext' hS fun w => (ht w).trans (ht' w).symm
    · intro h
      subst h
      refine M.ext' hS fun u => ⟨fun hu => ?_, fun hu => ?_⟩
      · obtain ⟨w, hw, hfw⟩ := hf1 u (hsx u hu)
        obtain ⟨u', hu', hfu'⟩ := (ht' w).mp ((ht w).mpr ⟨u, hu, hfw⟩)
        rw [(hf2 u u' w w (hsx u hu) (hsx' u' hu') hfw hfu').mpr rfl]
        exact hu'
      · obtain ⟨w, hw, hfw⟩ := hf1 u (hsx' u hu)
        obtain ⟨u', hu', hfu'⟩ := (ht w).mp ((ht' w).mpr ⟨u, hu, hfw⟩)
        rw [(hf2 u u' w w (hsx' u hu) (hsx u' hu') hfw hfu').mpr rfl]
        exact hu'

theorem eqv_pow {x y : V} (h : M.Eqv x y) : M.Eqv (M.pow x) (M.pow y) :=
  ⟨M.le_pow hS h.1, M.le_pow hS h.2⟩

/-- The singleton image of a power set and the power set of the singleton image are
equivalent. -/
theorem simg_pow (y : V) : M.Eqv (M.simg (M.pow y)) (M.pow (M.simg y)) := by
  obtain ⟨g, -, hg⟩ := M.comp (σSp [(0, 4), (4, 1), (5, 2), (6, 2), (7, 1)])
    (Fml.ex 4 (Fml.ex 5 (Fml.ex 6 (.and (fP 2 0 5 6) (.and (fS 1 5 4)
      (.all 7 (Fml.iff (.mem 7 6) (Fml.ex 8 (.and (.mem 8 4) (fS 0 7 8))))))))))
    0 rfl (fun _ => dflt)
  have hg' : ∀ p, M.mem p g ↔ ∃ s, p = M.op (M.sing s) (M.simg s) := by
    intro p
    rw [hg p]
    simp only [M.sat_ex, Sat, M.sat_iff, M.sat_fP 2 (p := 0) (a := 5) (b := 6) (by decide)
      (by decide) (by decide), M.sat_fS 1 (u := 5) (a := 4) (by decide) (by decide),
      M.sat_fS 0 (u := 7) (a := 8) (by decide) (by decide)]
    simp only [Function.update_apply]
    simp only [reduceIte, Nat.reduceEqDiff]
    constructor
    · rintro ⟨s, a, t, e1, e2, ht⟩
      refine ⟨s, ?_⟩
      have : t = M.simg s := M.ext' hS fun e => (ht e).trans M.mem_simg.symm
      rw [e1, e2, this]
    · rintro ⟨s, e⟩
      exact ⟨s, M.sing s, M.simg s, e, rfl, fun e => M.mem_simg⟩
  have hinj : M.Inj g (M.simg (M.pow y)) (M.pow (M.simg y)) := by
    refine ⟨fun a ha => ?_, fun a a' t t' ha ha' hp hp' => ?_⟩
    · obtain ⟨s, hs, rfl⟩ := M.mem_simg.mp ha
      refine ⟨M.simg s, (M.mem_pow' hS).mpr fun z hz => ?_, (hg' _).mpr ⟨s, rfl⟩⟩
      obtain ⟨d, hd, rfl⟩ := M.mem_simg.mp hz
      exact M.mem_simg.mpr ⟨d, (M.mem_pow' hS).mp hs d hd, rfl⟩
    · obtain ⟨s, e⟩ := (hg' _).mp hp
      obtain ⟨s', e'⟩ := (hg' _).mp hp'
      obtain ⟨e1, e2⟩ := M.op_inj e
      obtain ⟨e3, e4⟩ := M.op_inj e'
      subst e1 e2 e3 e4
      exact ⟨fun h => by rw [M.sing_inj h], fun h => by rw [M.simg_inj hS h]⟩
  refine ⟨⟨g, hinj⟩, M.le_conv hinj fun t ht => ?_⟩
  have ht' := (M.mem_pow' hS).mp ht
  have hsing : ∀ e, M.mem e t → ∃ d, e = M.sing d := fun e he => by
    obtain ⟨d, -, rfl⟩ := M.mem_simg.mp (ht' e he)
    exact ⟨d, rfl⟩
  refine ⟨M.sing (M.sUnion t), M.mem_simg.mpr ⟨M.sUnion t, (M.mem_pow' hS).mpr fun d hd => ?_, rfl⟩,
    (hg' _).mpr ⟨M.sUnion t, by rw [M.simg_sUnion hS hsing]⟩⟩
  obtain ⟨z, hz, hdz⟩ := M.mem_sUnion.mp hd
  obtain ⟨d', hd', rfl⟩ := M.mem_simg.mp (ht' z hz)
  rw [M.mem_sing.mp hdz]
  exact hd'

/-- **Cantor's theorem**: the power set of `y` does not inject into the singleton image of
`y`. -/
theorem cantor (y : V) : ¬ M.Le (M.pow y) (M.simg y) := by
  rintro ⟨f, hf1, hf2⟩
  obtain ⟨D, -, hD⟩ := M.comp (σSp [(0, 0), (1, 4), (2, 1), (4, 1), (5, 1), (6, 0)])
    (.and (.mem 0 2) (Fml.ex 4 (Fml.ex 5 (.and (.all 6 (Fml.imp (.mem 6 4) (.mem 6 2)))
      (.and (fS 0 5 0) (.and (fI 1 4 5 1) (.neg (.mem 0 4))))))))
    0 rfl (Function.update (Function.update (fun _ => dflt) 1 f) 2 y)
  have hD' : ∀ a, M.mem a D ↔ M.mem a y ∧ ∃ s, (∀ d, M.mem d s → M.mem d y) ∧
      M.mem (M.op s (M.sing a)) f ∧ ¬ M.mem a s := by
    intro a
    rw [hD a]
    simp [M.sat_ex, Sat, M.sat_imp, M.sat_fS, M.sat_fI, Function.update_apply]
  have hDy : M.mem D (M.pow y) := (M.mem_pow' hS).mpr fun a ha => ((hD' a).mp ha).1
  obtain ⟨w, hw, hfw⟩ := hf1 D hDy
  obtain ⟨d, hd, rfl⟩ := M.mem_simg.mp hw
  by_cases hdD : M.mem d D
  · obtain ⟨-, s, hs, hfs, hds⟩ := (hD' d).mp hdD
    have e : s = D := (hf2 s D (M.sing d) (M.sing d) ((M.mem_pow' hS).mpr hs) hDy hfs hfw).mpr rfl
    rw [e] at hds
    exact hds hdD
  · exact hdD ((hD' d).mpr ⟨hd, D, fun a ha => ((hD' a).mp ha).1, hfw, hdD⟩)

/-- The universe does not inject into the set of all singletons. -/
theorem cantor_univ : ¬ M.Le M.univ (M.simg M.univ) := by
  have h := M.cantor hS M.univ
  rwa [M.pow_univ hS] at h

/-- A set that injects into the set of all singletons is equivalent to a singleton image. -/
theorem exists_simg_eqv {x : V} (h : M.Le x (M.simg M.univ)) : ∃ y, M.Eqv x (M.simg y) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨hsub, h1, h2⟩ := M.inj_img hf
  have hsing : ∀ e, M.mem e (M.img f x) → ∃ d, e = M.sing d := fun e he => by
    obtain ⟨d, -, rfl⟩ := M.mem_simg.mp (hsub e he)
    exact ⟨d, rfl⟩
  refine ⟨M.sUnion (M.img f x), ?_⟩
  rw [M.simg_sUnion hS hsing]
  exact ⟨h1, h2⟩

end nf

theorem simg_le_univ (y : V) : M.Le (M.simg y) (M.simg M.univ) :=
  M.le_simg (M.le_of_sub fun a _ => M.mem_univ a)

end Model

end NFUCut



/-!
# Specker's theorem, part 2: the length of the Specker sequence modulo 3

For a set `x`, the *exponential* is defined when `x ≼ ι"V`: then `x ≈ ι"y` for some `y`, and
the exponential is `𝒫 y` (up to `≈`). The Specker sequence of `x` is `x, exp x, exp (exp x), …`,
as long as the exponential is defined. The relation `L` below relates `x` to the length of
its Specker sequence modulo 3, when the sequence is finite. The lengths are three fixed
objects `r0`, `r1`, `r2`, so no arithmetic is needed.

The key lemma `L_T` is Specker's: the sequence of `ι"x` is longer by one or two than the
"same" length for `x`.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V)

/-! ## The relation `≼` as a set -/

theorem exists_LeSet : ∃ R, ∀ p, M.mem p R ↔ ∃ x y, p = M.op x y ∧ M.Le x y := by
  obtain ⟨R, -, h⟩ := M.comp (σSp [(0, 3), (1, 1), (2, 1), (3, 3)])
    (Fml.ex 1 (Fml.ex 2 (.and (fP 1 0 1 2) (Fml.ex 3 (.and
      (.all 4 (Fml.imp (.mem 4 1) (Fml.ex 5 (.and (.mem 5 2) (fI 0 4 5 3)))))
      (.all 4 (.all 6 (.all 5 (.all 7 (Fml.imp (.mem 4 1) (Fml.imp (.mem 6 1)
        (Fml.imp (fI 0 4 5 3) (Fml.imp (fI 0 6 7 3) (Fml.iff (.eq 4 6) (.eq 5 7)))))))))))))))
    0 rfl (fun _ => dflt)
  refine ⟨R, fun p => ?_⟩
  rw [h p]
  simp [M.sat_ex, Sat, M.sat_imp, M.sat_iff, M.sat_fP, M.sat_fI, Function.update_apply, Le, Inj]

/-- The set of the pairs `⟨x, y⟩` with `x ≼ y`. -/
noncomputable def LeSet : V := Classical.choose M.exists_LeSet

theorem mem_LeSet {x y : V} : M.mem (M.op x y) M.LeSet ↔ M.Le x y := by
  refine (Classical.choose_spec M.exists_LeSet _).trans ⟨?_, fun h => ⟨x, y, rfl, h⟩⟩
  rintro ⟨x', y', e, h⟩
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact h

theorem exists_cap (A B : V) : ∃ C, ∀ p, M.mem p C ↔ M.mem p A ∧ M.mem p B := by
  obtain ⟨C, -, h⟩ := M.comp (fun i => if i = 0 then 0 else 1) (.and (.mem 0 1) (.mem 0 2)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 A) 2 B)
  refine ⟨C, fun p => ?_⟩
  rw [h p]
  simp [Sat, Function.update_apply]

/-! ## The three lengths -/

/-- Length `0` modulo 3. -/
noncomputable def r0 : V := M.emp

/-- Length `1` modulo 3. -/
noncomputable def r1 : V := M.zero

/-- Length `2` modulo 3. -/
noncomputable def r2 : V := M.univ

theorem r0_ne_r1 : M.r0 ≠ M.r1 := by
  intro h
  have h' : M.emp = M.zero := h
  have : M.mem M.emp M.zero := M.mem_zero.mpr rfl
  rw [← h'] at this
  exact M.not_mem_emp _ this

theorem r0_ne_r2 : M.r0 ≠ M.r2 := by
  intro h
  have h' : M.emp = M.univ := h
  have : M.mem M.emp M.univ := M.mem_univ _
  rw [← h'] at this
  exact M.not_mem_emp _ this

theorem r1_ne_r2 : M.r1 ≠ M.r2 := by
  intro h
  have h' : M.zero = M.univ := h
  have : M.mem M.zero M.univ := M.mem_univ _
  rw [← h'] at this
  exact M.r0_ne_r1 (M.mem_zero.mp this).symm

/-- The successor on the lengths modulo 3. -/
def Nx (r s : V) : Prop :=
  (r = M.r0 ∧ s = M.r1) ∨ (r = M.r1 ∧ s = M.r2) ∨ (r = M.r2 ∧ s = M.r0)

theorem nx_fun {r s s' : V} (h : M.Nx r s) (h' : M.Nx r s') : s = s' := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h' with ⟨a', b'⟩ | ⟨a', b'⟩ | ⟨a', b'⟩ <;>
    first
    | exact b.trans b'.symm
    | exact absurd (a.symm.trans a') M.r0_ne_r1
    | exact absurd (a'.symm.trans a) M.r0_ne_r1
    | exact absurd (a.symm.trans a') M.r1_ne_r2
    | exact absurd (a'.symm.trans a) M.r1_ne_r2
    | exact absurd (a.symm.trans a') M.r0_ne_r2
    | exact absurd (a'.symm.trans a) M.r0_ne_r2

theorem nx_res {r s : V} (h : M.Nx r s) : s = M.r0 ∨ s = M.r1 ∨ s = M.r2 := by
  rcases h with ⟨-, b⟩ | ⟨-, b⟩ | ⟨-, b⟩
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr b)
  · exact Or.inl b

theorem nx_total {s : V} (h : s = M.r0 ∨ s = M.r1 ∨ s = M.r2) : ∃ t, M.Nx s t := by
  rcases h with h | h | h
  · exact ⟨M.r1, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨M.r2, Or.inr (Or.inl ⟨h, rfl⟩)⟩
  · exact ⟨M.r0, Or.inr (Or.inr ⟨h, rfl⟩)⟩

theorem nx_irrefl {r : V} (h : M.Nx r r) : False := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact M.r0_ne_r1 (a.symm.trans b)
  · exact M.r1_ne_r2 (a.symm.trans b)
  · exact M.r0_ne_r2 (b.symm.trans a)

theorem nx_two {r s : V} (h : M.Nx r s) (h' : M.Nx s r) : False := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h' with ⟨a', b'⟩ | ⟨a', b'⟩ | ⟨a', b'⟩ <;>
    first
    | exact M.r0_ne_r1 (a.symm.trans b')
    | exact M.r0_ne_r1 (b'.symm.trans a)
    | exact M.r1_ne_r2 (a.symm.trans b')
    | exact M.r1_ne_r2 (b'.symm.trans a)
    | exact M.r0_ne_r2 (a.symm.trans b')
    | exact M.r0_ne_r2 (b'.symm.trans a)
    | exact M.r0_ne_r1 (a'.symm.trans b)
    | exact M.r0_ne_r1 (b.symm.trans a')
    | exact M.r1_ne_r2 (a'.symm.trans b)
    | exact M.r1_ne_r2 (b.symm.trans a')
    | exact M.r0_ne_r2 (a'.symm.trans b)
    | exact M.r0_ne_r2 (b.symm.trans a')

/-- The formula for `Nx`, with the three lengths as the values of `n0`, `n1`, `n2`. -/
def fNx (r s n0 n1 n2 : ℕ) : Fml :=
  Fml.or (.and (.eq r n0) (.eq s n1)) (Fml.or (.and (.eq r n1) (.eq s n2)) (.and (.eq r n2) (.eq s n0)))

/-! ## The exponential -/

variable [hNF : Fact (∀ x : V, M.isSet x)]

/-- The set of all singletons. -/
noncomputable def U1 : V := M.simg M.univ

theorem simg_eq_iff {sy y : V} :
    (∀ e, M.mem e sy ↔ ∃ d, M.mem d y ∧ e = M.sing d) ↔ sy = M.simg y :=
  ⟨fun h => M.ext' hNF.out fun e => (h e).trans M.mem_simg.symm, fun h e => h ▸ M.mem_simg⟩

theorem eq_pow_iff' {py y : V} :
    (∀ e, M.mem e py ↔ ∀ d, M.mem d e → M.mem d y) ↔ py = M.pow y :=
  ⟨fun h => M.ext' hNF.out fun e => (h e).trans (M.mem_pow' hNF.out).symm,
    fun h e => h ▸ M.mem_pow' hNF.out⟩

theorem exists_Ex : ∃ E, ∀ p, M.mem p E ↔ ∃ x y, p = M.op x (M.pow y) ∧ M.Eqv x (M.simg y) := by
  obtain ⟨E, -, h⟩ := M.comp
    (σSp [(0, 4), (1, 2), (2, 1), (3, 2), (4, 2), (5, 5), (6, 1), (8, 1)])
    (Fml.ex 1 (Fml.ex 2 (Fml.ex 3 (Fml.ex 4 (.and (fP 2 0 1 4)
      (.and (.all 6 (Fml.iff (.mem 6 3) (Fml.ex 7 (.and (.mem 7 2) (fS 0 6 7)))))
      (.and (.all 8 (Fml.iff (.mem 8 4) (.all 9 (Fml.imp (.mem 9 8) (.mem 9 2)))))
      (.and (fI 2 1 3 5) (fI 2 3 1 5)))))))))
    0 rfl (Function.update (fun _ => dflt) 5 M.LeSet)
  refine ⟨E, fun p => ?_⟩
  rw [h p]
  simp only [M.sat_ex, Sat, M.sat_iff, M.sat_imp,
    M.sat_fP 2 (p := 0) (a := 1) (b := 4) (by decide) (by decide) (by decide),
    M.sat_fS 0 (u := 6) (a := 7) (by decide) (by decide),
    M.sat_fI 2 (a := 1) (b := 3) (f := 5) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 3) (b := 1) (f := 5) (by decide) (by decide) (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff]
  constructor
  · rintro ⟨x, y, sy, py, e, h1, h2, h3, h4⟩
    have e1 : sy = M.simg y := M.simg_eq_iff.mp h1
    have e2 : py = M.pow y := M.eq_pow_iff'.mp h2
    subst e1 e2
    exact ⟨x, y, e, M.mem_LeSet.mp h3, M.mem_LeSet.mp h4⟩
  · rintro ⟨x, y, e, h3, h4⟩
    exact ⟨x, y, M.simg y, M.pow y, e, M.simg_eq_iff.mpr rfl, M.eq_pow_iff'.mpr rfl,
      M.mem_LeSet.mpr h3, M.mem_LeSet.mpr h4⟩

/-- The exponential as a relation: the pairs `⟨x, 𝒫 y⟩` with `x ≈ ι"y`. -/
noncomputable def Ex : V := Classical.choose M.exists_Ex

theorem mem_Ex {x q : V} : M.mem (M.op x q) M.Ex ↔ ∃ y, q = M.pow y ∧ M.Eqv x (M.simg y) := by
  refine (Classical.choose_spec M.exists_Ex _).trans ⟨?_, fun ⟨y, e, h⟩ => ⟨x, y, by rw [e], h⟩⟩
  rintro ⟨x', y, e, h⟩
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1]
  exact ⟨y, e2, h⟩

theorem Ex_le {x q : V} (h : M.mem (M.op x q) M.Ex) : M.Le x M.U1 := by
  obtain ⟨y, -, hxy⟩ := M.mem_Ex.mp h
  exact M.le_trans' hxy.1 (M.simg_le_univ y)

theorem Ex_congr {x x' q : V} (h : M.mem (M.op x q) M.Ex) (e : M.Eqv x x') :
    M.mem (M.op x' q) M.Ex := by
  obtain ⟨y, hq, hxy⟩ := M.mem_Ex.mp h
  exact M.mem_Ex.mpr ⟨y, hq, M.eqv_trans (M.eqv_symm e) hxy⟩

theorem Ex_fun {x q q' : V} (h : M.mem (M.op x q) M.Ex) (h' : M.mem (M.op x q') M.Ex) :
    M.Eqv q q' := by
  obtain ⟨y, e, hxy⟩ := M.mem_Ex.mp h
  obtain ⟨y', e', hxy'⟩ := M.mem_Ex.mp h'
  rw [e, e']
  exact M.eqv_pow hNF.out (M.eqv_of_simg (M.eqv_trans (M.eqv_symm hxy) hxy'))

theorem Ex_simg (x : V) : M.mem (M.op (M.simg x) (M.pow x)) M.Ex :=
  M.mem_Ex.mpr ⟨x, rfl, M.eqv_rfl _⟩

/-! ## The relation `L` -/

/-- The closure conditions that define `L`. -/
def Cl (S : V) : Prop :=
  (∀ x, ¬ M.Le x M.U1 → M.mem (M.op x M.r1) S) ∧
    ∀ x q r r', M.mem (M.op x q) M.Ex → M.mem (M.op q r) S → M.Nx r r' → M.mem (M.op x r') S

theorem exists_L : ∃ L, ∀ p, M.mem p L ↔ ∀ S, M.Cl S → M.mem p S := by
  obtain ⟨L, -, h⟩ := M.comp
    (σSp [(0, 4), (1, 5), (2, 2), (3, 5), (4, 5), (5, 2), (6, 2), (7, 2), (8, 2), (9, 2), (10, 2),
      (11, 2)])
    (.all 1 (Fml.imp (.and
        (.all 8 (Fml.imp (.neg (fI 2 8 2 3)) (fI 2 8 6 1)))
        (.all 8 (.all 9 (.all 10 (.all 11 (Fml.imp (fI 2 8 9 4) (Fml.imp (fI 2 9 10 1)
          (Fml.imp (fNx 10 11 5 6 7) (fI 2 8 11 1)))))))))
      (.mem 0 1)))
    0 rfl (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (fun _ => dflt) 2 M.U1) 3 M.LeSet) 4 M.Ex) 5 M.r0) 6 M.r1) 7 M.r2)
  refine ⟨L, fun p => ?_⟩
  rw [h p]
  simp only [Sat, M.sat_imp, M.sat_or, fNx,
    M.sat_fI 2 (a := 8) (b := 2) (f := 3) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 8) (b := 6) (f := 1) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 8) (b := 9) (f := 4) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 9) (b := 10) (f := 1) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 8) (b := 11) (f := 1) (by decide) (by decide) (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff]
  simp only [M.mem_LeSet]
  rfl

/-- The pairs `⟨x, r⟩` such that the Specker sequence of `x` is finite and its length is `r`
modulo 3. -/
noncomputable def L : V := Classical.choose M.exists_L

theorem mem_L {p : V} : M.mem p M.L ↔ ∀ S, M.Cl S → M.mem p S := Classical.choose_spec M.exists_L p

theorem L_cl : M.Cl M.L :=
  ⟨fun x hx => M.mem_L.mpr fun S hS => hS.1 x hx,
    fun x q r r' h1 h2 h3 => M.mem_L.mpr fun S hS => hS.2 x q r r' h1 (M.mem_L.mp h2 S hS) h3⟩

theorem L_min {S : V} (h : M.Cl S) {p : V} (hp : M.mem p M.L) : M.mem p S := M.mem_L.mp hp S h

/-- Induction on `L`, for a property given by a set. -/
theorem L_ind {A : V} (h1 : ∀ x, ¬ M.Le x M.U1 → M.mem (M.op x M.r1) A)
    (h2 : ∀ x q r r', M.mem (M.op x q) M.Ex → M.mem (M.op q r) M.L → M.mem (M.op q r) A →
      M.Nx r r' → M.mem (M.op x r') A) {p : V} (hp : M.mem p M.L) : M.mem p A := by
  obtain ⟨C, hC⟩ := M.exists_cap M.L A
  have hcl : M.Cl C :=
    ⟨fun x hx => (hC _).mpr ⟨M.L_cl.1 x hx, h1 x hx⟩,
      fun x q r r' hq hr hn => (hC _).mpr ⟨M.L_cl.2 x q r r' hq ((hC _).mp hr).1 hn,
        h2 x q r r' hq ((hC _).mp hr).1 ((hC _).mp hr).2 hn⟩⟩
  exact ((hC _).mp (M.L_min hcl hp)).2

theorem exists_invSet : ∃ A, ∀ p, M.mem p A ↔
    (∃ x, p = M.op x M.r1 ∧ ¬ M.Le x M.U1) ∨
      ∃ x q r r', p = M.op x r' ∧ M.mem (M.op x q) M.Ex ∧ M.mem (M.op q r) M.L ∧ M.Nx r r' := by
  obtain ⟨A, -, h⟩ := M.comp
    (σSp [(0, 4), (1, 5), (2, 2), (3, 5), (4, 5), (5, 2), (6, 2), (7, 2), (8, 2), (9, 2), (10, 2),
      (11, 2)])
    (Fml.or (Fml.ex 8 (.and (fP 2 0 8 6) (.neg (fI 2 8 2 3))))
      (Fml.ex 8 (Fml.ex 9 (Fml.ex 10 (Fml.ex 11 (.and (fP 2 0 8 11) (.and (fI 2 8 9 4)
        (.and (fI 2 9 10 1) (fNx 10 11 5 6 7)))))))))
    0 rfl (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 1 M.L) 2 M.U1) 3 M.LeSet) 4 M.Ex) 5 M.r0)
      6 M.r1) 7 M.r2)
  refine ⟨A, fun p => ?_⟩
  rw [h p]
  simp only [Sat, M.sat_ex, M.sat_or, fNx,
    M.sat_fP 2 (p := 0) (a := 8) (b := 6) (by decide) (by decide) (by decide),
    M.sat_fP 2 (p := 0) (a := 8) (b := 11) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 8) (b := 2) (f := 3) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 8) (b := 9) (f := 4) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 9) (b := 10) (f := 1) (by decide) (by decide) (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff]
  simp only [M.mem_LeSet]
  rfl

/-- Inversion for `L`. -/
theorem L_inv {x s : V} (h : M.mem (M.op x s) M.L) :
    (s = M.r1 ∧ ¬ M.Le x M.U1) ∨
      ∃ q r, M.mem (M.op x q) M.Ex ∧ M.mem (M.op q r) M.L ∧ M.Nx r s := by
  obtain ⟨A, hA⟩ := M.exists_invSet
  have key : M.mem (M.op x s) A :=
    M.L_ind (A := A) (fun x hx => (hA _).mpr (Or.inl ⟨x, rfl, hx⟩))
      (fun x q r r' hq hr _ hn => (hA _).mpr (Or.inr ⟨x, q, r, r', rfl, hq, hr, hn⟩)) h
  rcases (hA _).mp key with ⟨x', e, hx'⟩ | ⟨x', q, r, r', e, hq, hr, hn⟩
  · obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1]
    exact Or.inl ⟨e2, hx'⟩
  · obtain ⟨e1, e2⟩ := M.op_inj e
    rw [e1, e2]
    exact Or.inr ⟨q, r, hq, hr, hn⟩

theorem L_congr {x x' s : V} (h : M.mem (M.op x s) M.L) (e : M.Eqv x x') :
    M.mem (M.op x' s) M.L := by
  rcases M.L_inv h with ⟨hs, hx⟩ | ⟨q, r, hq, hr, hn⟩
  · rw [hs]
    exact M.L_cl.1 x' fun h' => hx (M.le_trans' e.1 h')
  · exact M.L_cl.2 x' q r s (M.Ex_congr hq e) hr hn

theorem L_res {x s : V} (h : M.mem (M.op x s) M.L) : s = M.r0 ∨ s = M.r1 ∨ s = M.r2 := by
  rcases M.L_inv h with ⟨hs, -⟩ | ⟨q, r, -, -, hn⟩
  · exact Or.inr (Or.inl hs)
  · exact M.nx_res hn

theorem exists_funSet : ∃ A, ∀ p, M.mem p A ↔
    ∃ x r, p = M.op x r ∧ ∀ s, M.mem (M.op x s) M.L → s = r := by
  obtain ⟨A, -, h⟩ := M.comp (σSp [(0, 4), (1, 5), (8, 2), (10, 2), (11, 2)])
    (Fml.ex 8 (Fml.ex 10 (.and (fP 2 0 8 10) (.all 11 (Fml.imp (fI 2 8 11 1) (.eq 11 10))))))
    0 rfl (Function.update (fun _ => dflt) 1 M.L)
  refine ⟨A, fun p => ?_⟩
  rw [h p]
  simp only [Sat, M.sat_ex, M.sat_imp,
    M.sat_fP 2 (p := 0) (a := 8) (b := 10) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 8) (b := 11) (f := 1) (by decide) (by decide) (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff]

/-- The length is unique. -/
theorem L_fun {x s s' : V} (h : M.mem (M.op x s) M.L) (h' : M.mem (M.op x s') M.L) : s' = s := by
  obtain ⟨A, hA⟩ := M.exists_funSet
  have key : M.mem (M.op x s) A := by
    refine M.L_ind (A := A) (fun x hx => ?_) (fun x q r r' hq hrL hrA hn => ?_) h
    · refine (hA _).mpr ⟨x, M.r1, rfl, fun t ht => ?_⟩
      rcases M.L_inv ht with ⟨e, -⟩ | ⟨q, r, hq, -, -⟩
      · exact e
      · exact absurd (M.Ex_le hq) hx
    · obtain ⟨q1, ra, e, hr⟩ := (hA _).mp hrA
      obtain ⟨e1, e2⟩ := M.op_inj e
      subst e1 e2
      refine (hA _).mpr ⟨x, r', rfl, fun t ht => ?_⟩
      rcases M.L_inv ht with ⟨-, hx⟩ | ⟨q2, rb, hq2, hr2, hn2⟩
      · exact absurd (M.Ex_le hq) hx
      · have e2 : rb = r := hr rb (M.L_congr hr2 (M.Ex_fun hq2 hq))
        rw [e2] at hn2
        exact M.nx_fun hn2 hn
  obtain ⟨x1, ra, e, hr⟩ := (hA _).mp key
  obtain ⟨e1, e2⟩ := M.op_inj e
  subst e1 e2
  exact hr s' h'

/-! ## Specker's lemma -/

theorem exists_TSet : ∃ A, ∀ p, M.mem p A ↔ ∃ x r, p = M.op x r ∧ ∃ s s', M.Nx r s ∧ M.Nx s s' ∧
    (M.mem (M.op (M.simg x) s) M.L ∨ M.mem (M.op (M.simg x) s') M.L) := by
  obtain ⟨A, -, h⟩ := M.comp
    (σSp [(0, 4), (8, 2), (10, 2), (12, 3), (13, 3), (14, 3), (15, 6), (5, 2), (6, 2), (7, 2),
      (16, 3), (17, 3), (18, 3), (19, 2), (20, 1)])
    (Fml.ex 8 (Fml.ex 10 (.and (fP 2 0 8 10) (Fml.ex 12 (Fml.ex 13 (Fml.ex 14 (.and
      (.all 19 (Fml.iff (.mem 19 12) (Fml.ex 20 (.and (.mem 20 8) (fS 1 19 20)))))
      (.and (Fml.or (.and (.eq 10 5) (.eq 13 17)) (Fml.or (.and (.eq 10 6) (.eq 13 18))
            (.and (.eq 10 7) (.eq 13 16))))
        (.and (fNx 13 14 16 17 18)
          (Fml.or (fI 3 12 13 15) (fI 3 12 14 15)))))))))))
    0 rfl (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => dflt) 15 M.L) 5 M.r0) 6 M.r1) 7 M.r2)
      16 M.r0) 17 M.r1) 18 M.r2)
  refine ⟨A, fun p => ?_⟩
  rw [h p]
  simp only [Sat, M.sat_ex, M.sat_or, M.sat_iff, fNx,
    M.sat_fP 2 (p := 0) (a := 8) (b := 10) (by decide) (by decide) (by decide),
    M.sat_fS 1 (u := 19) (a := 20) (by decide) (by decide),
    M.sat_fI 3 (a := 12) (b := 13) (f := 15) (by decide) (by decide) (by decide),
    M.sat_fI 3 (a := 12) (b := 14) (f := 15) (by decide) (by decide) (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff]
  constructor
  · rintro ⟨x, r, e, tx, s, s', h1, h2, h3, h4⟩
    have e1 : tx = M.simg x := M.simg_eq_iff.mp h1
    subst e1
    exact ⟨x, r, e, s, s', h2, h3, h4⟩
  · rintro ⟨x, r, e, s, s', h2, h3, h4⟩
    exact ⟨x, r, e, M.simg x, s, s', M.simg_eq_iff.mpr rfl, h2, h3, h4⟩

section comparable

/- The hypothesis of Specker's lemma: a set that does not inject into the set of all
singletons includes a copy of it. -/
variable (Hc : ∀ x : V, ¬ M.Le x M.U1 → M.Le M.U1 x)
include Hc

/-- **Specker's lemma.** If the Specker sequence of `x` is finite of length `r`, then the
sequence of `ι"x` is finite, of length `r + 1` or `r + 2` (modulo 3). -/
theorem L_T {x r : V} (h : M.mem (M.op x r) M.L) : ∃ s s', M.Nx r s ∧ M.Nx s s' ∧
    (M.mem (M.op (M.simg x) s) M.L ∨ M.mem (M.op (M.simg x) s') M.L) := by
  have hS := hNF.out
  obtain ⟨A, hA⟩ := M.exists_TSet
  have key : M.mem (M.op x r) A := by
    refine M.L_ind (A := A) (fun x hx => ?_) (fun x q r r' hq hrL hrA hn => ?_) h
    · refine (hA _).mpr ⟨x, M.r1, rfl, M.r2, M.r0, Or.inr (Or.inl ⟨rfl, rfl⟩),
        Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
      have hUx := Hc x hx
      by_cases hp : M.Le (M.pow x) M.U1
      · right
        obtain ⟨y, hy⟩ := M.exists_simg_eqv hS hp
        have hny : ¬ M.Le (M.pow y) M.U1 := by
          intro hpy
          have h1 : M.Le M.U1 (M.pow M.U1) := by
            have h0 := (M.simg_pow hS M.univ).1
            rw [M.pow_univ hS] at h0
            exact h0
          have h2 : M.Le (M.pow M.U1) (M.pow x) := M.le_pow hS hUx
          have h3 : M.Le M.U1 (M.simg y) := M.le_trans' h1 (M.le_trans' h2 hy.1)
          have h4 : M.Le M.univ y := M.le_of_simg h3
          have h5 : M.Le M.univ (M.pow y) := by
            have h0 := M.le_pow hS h4
            rwa [M.pow_univ hS] at h0
          exact M.cantor_univ hS (M.le_trans' h5 hpy)
        have l1 : M.mem (M.op (M.pow y) M.r1) M.L := M.L_cl.1 _ hny
        have l2 : M.mem (M.op (M.pow x) M.r2) M.L :=
          M.L_cl.2 _ _ _ _ (M.mem_Ex.mpr ⟨y, rfl, hy⟩) l1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        exact M.L_cl.2 _ _ _ _ (M.Ex_simg x) l2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · left
        exact M.L_cl.2 _ _ _ _ (M.Ex_simg x) (M.L_cl.1 _ hp) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · obtain ⟨q1, ra, e, s, s', hs, hs', hor⟩ := (hA _).mp hrA
      obtain ⟨e1, e2⟩ := M.op_inj e
      subst e1 e2
      obtain ⟨y, eq, hxy⟩ := M.mem_Ex.mp hq
      subst eq
      have es : s = r' := M.nx_fun hs hn
      subst es
      have hE : M.mem (M.op (M.simg x) (M.pow (M.simg y))) M.Ex :=
        M.mem_Ex.mpr ⟨M.simg y, rfl, M.eqv_simg hxy⟩
      obtain ⟨s'', hs''⟩ := M.nx_total (M.nx_res hs')
      refine (hA _).mpr ⟨x, s, rfl, s', s'', hs', hs'', ?_⟩
      rcases hor with h1 | h1
      · left
        exact M.L_cl.2 _ _ _ _ hE (M.L_congr h1 (M.simg_pow hS y)) hs'
      · right
        exact M.L_cl.2 _ _ _ _ hE (M.L_congr h1 (M.simg_pow hS y)) hs''
  obtain ⟨x1, ra, e, s, s', hs, hs', hor⟩ := (hA _).mp key
  obtain ⟨e1, e2⟩ := M.op_inj e
  subst e1 e2
  exact ⟨s, s', hs, hs', hor⟩

/-- **The contradiction.** No set with a finite Specker sequence is equivalent to its singleton
image. -/
theorem specker_core {x r : V} (h : M.mem (M.op x r) M.L) (hx : M.Eqv (M.simg x) x) : False := by
  obtain ⟨s, s', hs, hs', hor⟩ := M.L_T Hc h
  rcases hor with h1 | h1
  · have e := M.L_fun h (M.L_congr h1 hx)
    rw [e] at hs
    exact M.nx_irrefl hs
  · have e := M.L_fun h (M.L_congr h1 hx)
    rw [e] at hs'
    exact M.nx_two hs hs'

end comparable

/-! ## Reflection along the singleton image -/

theorem exists_RSet : ∃ A, ∀ p, M.mem p A ↔ ∃ z r, p = M.op z r ∧
    ∀ y, M.Eqv z (M.simg y) → ∃ r', M.mem (M.op y r') M.L := by
  obtain ⟨A, -, h⟩ := M.comp
    (σSp [(0, 5), (8, 3), (10, 3), (12, 2), (13, 3), (14, 2), (1, 5), (3, 6), (19, 2), (20, 1)])
    (Fml.ex 8 (Fml.ex 10 (.and (fP 3 0 8 10) (.all 12 (.all 13 (Fml.imp
      (.all 19 (Fml.iff (.mem 19 13) (Fml.ex 20 (.and (.mem 20 12) (fS 1 19 20)))))
      (Fml.imp (fI 3 8 13 3) (Fml.imp (fI 3 13 8 3) (Fml.ex 14 (fI 2 12 14 1))))))))))
    0 rfl (Function.update (Function.update (fun _ => dflt) 1 M.L) 3 M.LeSet)
  refine ⟨A, fun p => ?_⟩
  rw [h p]
  simp only [Sat, M.sat_ex, M.sat_imp, M.sat_iff,
    M.sat_fP 3 (p := 0) (a := 8) (b := 10) (by decide) (by decide) (by decide),
    M.sat_fS 1 (u := 19) (a := 20) (by decide) (by decide),
    M.sat_fI 3 (a := 8) (b := 13) (f := 3) (by decide) (by decide) (by decide),
    M.sat_fI 3 (a := 13) (b := 8) (f := 3) (by decide) (by decide) (by decide),
    M.sat_fI 2 (a := 12) (b := 14) (f := 1) (by decide) (by decide) (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff]
  constructor
  · rintro ⟨z, r, e, hz⟩
    exact ⟨z, r, e, fun y hy => hz y (M.simg y) (M.simg_eq_iff.mpr rfl) (M.mem_LeSet.mpr hy.1)
      (M.mem_LeSet.mpr hy.2)⟩
  · rintro ⟨z, r, e, hz⟩
    refine ⟨z, r, e, fun y sy h1 h2 h3 => ?_⟩
    have e1 : sy = M.simg y := M.simg_eq_iff.mp h1
    subst e1
    exact hz y ⟨M.mem_LeSet.mp h2, M.mem_LeSet.mp h3⟩

/-- If the Specker sequence of a set equivalent to `ι"y` is finite, so is that of `y`. -/
theorem L_refl {z r : V} (h : M.mem (M.op z r) M.L) {y : V} (hy : M.Eqv z (M.simg y)) :
    ∃ r', M.mem (M.op y r') M.L := by
  have hS := hNF.out
  obtain ⟨A, hA⟩ := M.exists_RSet
  have key : M.mem (M.op z r) A := by
    refine M.L_ind (A := A) (fun x hx => ?_) (fun x q r r' hq hrL hrA hn => ?_) h
    · refine (hA _).mpr ⟨x, M.r1, rfl, fun y hy => ?_⟩
      exact absurd (M.le_trans' hy.1 (M.simg_le_univ y)) hx
    · obtain ⟨q1, ra, e, ih⟩ := (hA _).mp hrA
      obtain ⟨e1, e2⟩ := M.op_inj e
      subst e1 e2
      obtain ⟨w, eq, hxw⟩ := M.mem_Ex.mp hq
      subst eq
      refine (hA _).mpr ⟨x, r', rfl, fun y hy => ?_⟩
      have hwy : M.Eqv w y := M.eqv_of_simg (M.eqv_trans (M.eqv_symm hxw) hy)
      by_cases hyU : M.Le y M.U1
      · obtain ⟨u, hu⟩ := M.exists_simg_eqv hS hyU
        have h1 : M.Eqv (M.pow w) (M.simg (M.pow u)) :=
          M.eqv_trans (M.eqv_pow hS (M.eqv_trans hwy hu)) (M.eqv_symm (M.simg_pow hS u))
        obtain ⟨r'', hr''⟩ := ih (M.pow u) h1
        obtain ⟨t, ht⟩ := M.nx_total (M.L_res hr'')
        exact ⟨t, M.L_cl.2 _ _ _ _ (M.mem_Ex.mpr ⟨u, rfl, hu⟩) hr'' ht⟩
      · exact ⟨M.r1, M.L_cl.1 _ hyU⟩
  obtain ⟨z1, ra, e, ih⟩ := (hA _).mp key
  obtain ⟨e1, e2⟩ := M.op_inj e
  subst e1 e2
  exact ih y hy

end Model

end NFUCut



/-!
# Specker's theorem, part 3: NF proves Infinity, and the sets are not well-ordered by `≼`

If the universe is finite, any two sets are comparable and every nonempty set of sets has a
largest member for `≼`. Then the Specker sequence of the empty set is finite, and the empty set
is its own singleton image, which contradicts Specker's lemma.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V)

/-! ## Finite sets -/

/-- Induction on finite sets, for a property given by a set. -/
theorem fin_ind {F : V} (h0 : M.mem M.emp F) (hs : ∀ s b, M.mem s F → M.mem (M.adj s b) F)
    {x : V} (hx : M.Fin x) : M.mem x F := by
  obtain ⟨-, k, hk, hxk⟩ := hx
  obtain ⟨I, -, hI⟩ := M.comp (fun i => if i = 1 then 1 else 2)
    (.all 1 (Fml.imp (.mem 1 0) (.mem 1 2))) 0 rfl (Function.update (fun _ => dflt) 2 F)
  have hI' : ∀ k, M.mem k I ↔ ∀ x, M.mem x k → M.mem x F := by
    intro k
    rw [hI k]
    simp [Sat, M.sat_imp, Function.update_apply]
  have key : M.mem k I := by
    refine M.nat_ind ((hI' _).mpr fun x hx => ?_) (fun k hk => (hI' _).mpr fun x hx => ?_) hk
    · rw [M.mem_zero.mp hx]
      exact h0
    · obtain ⟨y, b, hy, -, rfl⟩ := M.mem_succ.mp hx
      exact hs y b ((hI' k).mp hk y hy)
  exact (hI' k).mp key x hxk

variable [hNF : Fact (∀ x : V, M.isSet x)]

/-- A subset of a finite set is finite. -/
theorem fin_sub {x y : V} (hx : M.Fin x) (hyx : ∀ a, M.mem a y → M.mem a x) : M.Fin y := by
  have hS := hNF.out
  obtain ⟨F, -, hF⟩ := M.comp
    (fun i => if i = 2 then 0 else if i = 28 then 2 else if i = 3 then 3 else 1)
    (.all 1 (Fml.imp (.all 2 (Fml.imp (.mem 2 1) (.mem 2 0))) (fFin 1 3))) 0 rfl
    (Function.update (fun _ => dflt) 3 M.nat)
  have hF' : ∀ x, M.mem x F ↔ ∀ y, (∀ a, M.mem a y → M.mem a x) → M.Fin y := by
    intro x
    rw [hF x]
    simp only [Sat, M.sat_imp, M.sat_fFin (x := 1) (N := 3) (by decide) (by decide)]
    simp only [Function.update_apply]
    simp only [reduceIte, Nat.reduceEqDiff]
    rfl
  have key : M.mem x F := by
    refine M.fin_ind ((hF' _).mpr fun y hy => ?_) (fun s b hs => (hF' _).mpr fun y hy => ?_) hx
    · have : y = M.emp := M.eq_emp (hS y) fun a ha => M.not_mem_emp a (hy a ha)
      rw [this]
      exact M.fin_emp
    · by_cases hb : M.mem b y
      · obtain ⟨r, -, hr⟩ := M.exists_rem y b
        have hrs : ∀ a, M.mem a r → M.mem a s := fun a ha => by
          obtain ⟨hay, hab⟩ := (hr a).mp ha
          exact (M.mem_adj.mp (hy a hay)).resolve_right hab
        have hfr : M.Fin r := (hF' s).mp hs r hrs
        have e : M.adj r b = y := M.ext' hS fun a => by
          rw [M.mem_adj, hr a]
          constructor
          · rintro (⟨h, -⟩ | h)
            · exact h
            · rw [h]
              exact hb
          · intro h
            by_cases hab : a = b
            · exact Or.inr hab
            · exact Or.inl ⟨h, hab⟩
        rw [← e]
        exact M.fin_adj b hfr
      · refine (hF' s).mp hs y fun a ha => (M.mem_adj.mp (hy a ha)).resolve_right fun e => ?_
        rw [e] at ha
        exact hb ha
  exact (hF' x).mp key y hyx

/-- If Infinity fails, every set is finite. -/
theorem fin_all (hfin : ¬ M.Infinity) (x : V) : M.Fin x := by
  have h : ∃ n, M.mem n M.nat ∧ M.mem M.univ n := by
    by_contra hno
    exact hfin fun n hn hu => hno ⟨n, hn, hu⟩
  obtain ⟨n, hn, hu⟩ := h
  exact M.fin_sub ⟨M.univ_isSet, n, hn, hu⟩ fun a _ => M.mem_univ a

/-- An injection that is not onto extends to one more point. -/
theorem inj_extend {f s y b w0 : V} (hf : M.Inj f s y) (hb : ¬ M.mem b s) (hw : M.mem w0 y)
    (hw0 : ∀ u, M.mem u s → ¬ M.mem (M.op u w0) f) : M.Le (M.adj s b) y := by
  obtain ⟨g, -, hg⟩ := M.comp (σSp [(0, 2), (1, 3), (2, 1)])
    (Fml.or (.and (.mem 0 1) (Fml.ex 4 (Fml.ex 5 (.and (fP 0 0 4 5) (.mem 4 2))))) (fP 0 0 3 6))
    0 rfl (Function.update (Function.update (Function.update (Function.update (fun _ => dflt)
      1 f) 2 s) 3 b) 6 w0)
  have hg' : ∀ p, M.mem p g ↔ (M.mem p f ∧ ∃ u w, p = M.op u w ∧ M.mem u s) ∨ p = M.op b w0 := by
    intro p
    rw [hg p]
    simp [Sat, M.sat_ex, M.sat_or, M.sat_fP, Function.update_apply]
  refine ⟨g, fun u hu => ?_, fun u u' w w' hu hu' hp hp' => ?_⟩
  · rcases M.mem_adj.mp hu with h | h
    · obtain ⟨w, hw', hfw⟩ := hf.1 u h
      exact ⟨w, hw', (hg' _).mpr (Or.inl ⟨hfw, u, w, rfl, h⟩)⟩
    · rw [h]
      exact ⟨w0, hw, (hg' _).mpr (Or.inr rfl)⟩
  · rcases (hg' _).mp hp with ⟨hfp, u1, w1, e, hu1⟩ | e <;>
      rcases (hg' _).mp hp' with ⟨hfp', u1', w1', e', hu1'⟩ | e'
    · obtain ⟨e1, e2⟩ := M.op_inj e
      obtain ⟨e3, e4⟩ := M.op_inj e'
      subst e1 e2 e3 e4
      exact hf.2 u u' w w' hu1 hu1' hfp hfp'
    · obtain ⟨e1, e2⟩ := M.op_inj e
      obtain ⟨e3, e4⟩ := M.op_inj e'
      subst e1 e2 e3 e4
      constructor
      · intro h
        rw [h] at hu1
        exact absurd hu1 hb
      · intro h
        rw [h] at hfp
        exact absurd hfp (hw0 u hu1)
    · obtain ⟨e1, e2⟩ := M.op_inj e
      obtain ⟨e3, e4⟩ := M.op_inj e'
      subst e1 e2 e3 e4
      constructor
      · intro h
        rw [← h] at hu1'
        exact absurd hu1' hb
      · intro h
        rw [← h] at hfp'
        exact absurd hfp' (hw0 u' hu1')
    · obtain ⟨e1, e2⟩ := M.op_inj e
      obtain ⟨e3, e4⟩ := M.op_inj e'
      rw [e1, e2, e3, e4]
      exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- A finite set is comparable with every set. -/
theorem fin_compar {x : V} (hx : M.Fin x) (y : V) : M.Le x y ∨ M.Le y x := by
  obtain ⟨F, -, hF⟩ := M.comp (σSp [(0, 1), (1, 1), (2, 4)])
    (Fml.or (fI 1 0 1 2) (fI 1 1 0 2)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 y) 2 M.LeSet)
  have hF' : ∀ x, M.mem x F ↔ M.Le x y ∨ M.Le y x := by
    intro x
    rw [hF x]
    simp [Sat, M.sat_or, M.sat_fI, Function.update_apply, M.mem_LeSet]
  refine (hF' x).mp (M.fin_ind ((hF' _).mpr (Or.inl ?_)) (fun s b hs => (hF' _).mpr ?_) hx)
  · exact ⟨M.emp, fun u hu => absurd hu (M.not_mem_emp u),
      fun u u' w w' hu => absurd hu (M.not_mem_emp u)⟩
  · have hsub : ∀ a, M.mem a s → M.mem a (M.adj s b) := fun a ha => M.mem_adj.mpr (Or.inl ha)
    rcases (hF' s).mp hs with ⟨f, hf⟩ | h
    · by_cases hb : M.mem b s
      · left
        exact M.le_trans' (M.le_of_sub fun a ha => (M.mem_adj.mp ha).elim id (fun e => e ▸ hb))
          ⟨f, hf⟩
      · by_cases hsurj : ∀ w, M.mem w y → ∃ u, M.mem u s ∧ M.mem (M.op u w) f
        · right
          exact M.le_trans' (M.le_conv hf hsurj) (M.le_of_sub hsub)
        · left
          have hex : ∃ w0, M.mem w0 y ∧ ∀ u, M.mem u s → ¬ M.mem (M.op u w0) f := by
            by_contra hno
            refine hsurj fun w hw => ?_
            by_contra hn
            exact hno ⟨w, hw, fun u hu hf' => hn ⟨u, hu, hf'⟩⟩
          obtain ⟨w0, hw, hw0⟩ := hex
          exact M.inj_extend hf hb hw hw0
    · right
      exact M.le_trans' h (M.le_of_sub hsub)

/-- A nonempty finite set of pairwise comparable sets has a largest member. -/
theorem fin_max (Hall : ∀ x y : V, M.Le x y ∨ M.Le y x) {X : V} (hX : M.Fin X) :
    (∀ x, ¬ M.mem x X) ∨ ∃ m, M.mem m X ∧ ∀ x, M.mem x X → M.Le x m := by
  obtain ⟨F, -, hF⟩ := M.comp (σSp [(0, 2), (1, 1), (2, 1), (3, 4)])
    (Fml.or (.all 1 (.neg (.mem 1 0)))
      (Fml.ex 2 (.and (.mem 2 0) (.all 1 (Fml.imp (.mem 1 0) (fI 1 1 2 3))))))
    0 rfl (Function.update (fun _ => dflt) 3 M.LeSet)
  have hF' : ∀ X, M.mem X F ↔
      (∀ x, ¬ M.mem x X) ∨ ∃ m, M.mem m X ∧ ∀ x, M.mem x X → M.Le x m := by
    intro X
    rw [hF X]
    simp [Sat, M.sat_or, M.sat_ex, M.sat_imp, M.sat_fI, Function.update_apply, M.mem_LeSet]
  refine (hF' X).mp (M.fin_ind ((hF' _).mpr (Or.inl fun x => M.not_mem_emp x))
    (fun s b hs => (hF' _).mpr (Or.inr ?_)) hX)
  rcases (hF' s).mp hs with h | ⟨m, hm, hmax⟩
  · refine ⟨b, M.mem_adj.mpr (Or.inr rfl), fun x hx => ?_⟩
    rcases M.mem_adj.mp hx with h' | h'
    · exact absurd h' (h x)
    · rw [h']
      exact M.le_rfl' b
  · rcases Hall b m with hbm | hmb
    · refine ⟨m, M.mem_adj.mpr (Or.inl hm), fun x hx => ?_⟩
      rcases M.mem_adj.mp hx with h' | h'
      · exact hmax x h'
      · rw [h']
        exact hbm
    · refine ⟨b, M.mem_adj.mpr (Or.inr rfl), fun x hx => ?_⟩
      rcases M.mem_adj.mp hx with h' | h'
      · exact M.le_trans' (hmax x h') hmb
      · rw [h']
        exact M.le_rfl' b

/-! ## The sets with a finite Specker sequence -/

theorem exists_domL : ∃ C, ∀ x, M.mem x C ↔ ∃ r, M.mem (M.op x r) M.L := by
  obtain ⟨C, -, hC⟩ := M.comp (σSp [(0, 2), (1, 5), (2, 2)]) (Fml.ex 2 (fI 2 0 2 1)) 0 rfl
    (Function.update (fun _ => dflt) 1 M.L)
  refine ⟨C, fun x => ?_⟩
  rw [hC x]
  simp [M.sat_ex, M.sat_fI, Function.update_apply]

theorem exists_codomL : ∃ X, ∀ x, M.mem x X ↔ ¬ ∃ r, M.mem (M.op x r) M.L := by
  obtain ⟨X, -, hX⟩ := M.comp (σSp [(0, 2), (1, 5), (2, 2)]) (.neg (Fml.ex 2 (fI 2 0 2 1))) 0 rfl
    (Function.update (fun _ => dflt) 1 M.L)
  refine ⟨X, fun x => ?_⟩
  rw [hX x]
  simp [Sat, M.sat_ex, M.sat_fI, Function.update_apply]

/-! ## Infinity -/

/-- **NF proves Infinity.** In a model of NF (a model of NFU in which every object is a set),
the universe belongs to no natural number. -/
theorem nf_infinity : M.Infinity := by
  have hS := hNF.out
  by_contra hfin
  have hall : ∀ x, M.Fin x := M.fin_all hfin
  have Hcomp : ∀ x y : V, M.Le x y ∨ M.Le y x := fun x y => M.fin_compar (hall x) y
  have Hc : ∀ x : V, ¬ M.Le x M.U1 → M.Le M.U1 x := fun x hx => (Hcomp x M.U1).resolve_left hx
  have hemp : ∃ r, M.mem (M.op M.emp r) M.L := by
    by_contra hno
    obtain ⟨X, hX⟩ := M.exists_codomL
    rcases M.fin_max Hcomp (hall X) with h | ⟨m, hm, hmax⟩
    · exact h M.emp ((hX _).mpr hno)
    · have hmL := (hX m).mp hm
      have hmU : M.Le m M.U1 := by
        by_contra h
        exact hmL ⟨M.r1, M.L_cl.1 m h⟩
      obtain ⟨y, hy⟩ := M.exists_simg_eqv hS hmU
      have hpy : M.mem (M.pow y) X := by
        rw [hX]
        rintro ⟨r, hr⟩
        obtain ⟨t, ht⟩ := M.nx_total (M.L_res hr)
        exact hmL ⟨t, M.L_cl.2 _ _ _ _ (M.mem_Ex.mpr ⟨y, rfl, hy⟩) hr ht⟩
      exact M.cantor hS y (M.le_trans' (hmax _ hpy) hy.1)
  obtain ⟨r, hr⟩ := hemp
  have hT : M.Eqv (M.simg M.emp) M.emp := by
    rw [M.simg_emp]
    exact M.eqv_rfl _
  exact M.specker_core Hc hr hT

/-! ## Specker's theorem -/

/-- **Specker's theorem**, in the form: the sets are not well-ordered by `≼`. If every set that
does not inject into the set of all singletons includes a copy of it (in particular, if any
two sets are comparable), then some nonempty set of sets has no least member for `≼`. -/
theorem specker (H1 : ∀ x : V, ¬ M.Le x M.U1 → M.Le M.U1 x)
    (H2 : ∀ C : V, (∃ x, M.mem x C) → ∃ x, M.mem x C ∧ ∀ y, M.mem y C → M.Le x y) : False := by
  have hS := hNF.out
  obtain ⟨C, hC⟩ := M.exists_domL
  have hne : ∃ x, M.mem x C :=
    ⟨M.univ, (hC _).mpr ⟨M.r1, M.L_cl.1 _ (M.cantor_univ hS)⟩⟩
  obtain ⟨x, hx, hmin⟩ := H2 C hne
  obtain ⟨r, hr⟩ := (hC x).mp hx
  obtain ⟨s, s', hs, hs', hor⟩ := M.L_T H1 hr
  have hTx : M.mem (M.simg x) C := (hC _).mpr (hor.elim (fun h => ⟨s, h⟩) (fun h => ⟨s', h⟩))
  have h1 : M.Le x (M.simg x) := hmin _ hTx
  have hxU : M.Le x M.U1 := M.le_trans' h1 (M.simg_le_univ x)
  obtain ⟨y, hy⟩ := M.exists_simg_eqv hS hxU
  obtain ⟨r', hr'⟩ := M.L_refl hr hy
  have h2 : M.Le x y := hmin _ ((hC _).mpr ⟨r', hr'⟩)
  have h3 : M.Le (M.simg x) x := M.le_trans' (M.le_simg h2) hy.2
  exact M.specker_core H1 hr ⟨h3, h1⟩

/-- The sets are not well-ordered by `≼`: it is not the case that any two sets are comparable
and every nonempty set of sets has a least member. -/
theorem not_wellOrdered_le :
    ¬ ((∀ x y : V, M.Le x y ∨ M.Le y x) ∧
      ∀ C : V, (∃ x, M.mem x C) → ∃ x, M.mem x C ∧ ∀ y, M.mem y C → M.Le x y) :=
  fun ⟨h1, h2⟩ => M.specker (fun x hx => (h1 x M.U1).resolve_left hx) h2

end Model

end NFUCut



/-!
# Specker's theorem, part 4: the universe of NF has no well-ordering

A well-ordering of the universe would make any two sets comparable for `≼`, and would give
every nonempty set of sets a least member for `≼`. This uses the comparability of
well-orderings from `NFUHartogs`, which is available because Infinity is now a theorem.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hNF : Fact (∀ x : V, M.isSet x)]

/-- In a model of NF, Infinity holds; this makes the library for NFU + Infinity available. -/
instance nf_infinity_fact : Fact M.Infinity := ⟨M.nf_infinity⟩

/-- `s` is the restriction of the relation `R` to the set `x`. -/
def IsRst (R x s : V) : Prop :=
  ∀ a b, M.mem (M.op a b) s ↔ M.mem (M.op a b) R ∧ M.mem a x ∧ M.mem b x

theorem exists_rst (R x : V) : ∃ s, M.IsRst R x s := by
  obtain ⟨s, -, hs⟩ := M.comp (σW [(0, 4), (1, 5), (2, 3)])
    (Fml.ex 12 (Fml.ex 13 (.and (fPr 0 12 13) (.and (fApp 1 12 13) (.and (.mem 12 2) (.mem 13 2))))))
    0 rfl (Function.update (Function.update (fun _ => dflt) 1 R) 2 x)
  have hs' : ∀ p, M.mem p s ↔ ∃ a b, p = M.op a b ∧ M.mem (M.op a b) R ∧ M.mem a x ∧ M.mem b x := by
    intro p
    rw [hs p]
    simp [Sat, M.sat_ex, M.sat_fPr, M.sat_fApp, Function.update_apply]
  refine ⟨s, fun a b => ⟨fun h => ?_, fun h => (hs' _).mpr ⟨a, b, rfl, h⟩⟩⟩
  obtain ⟨a', b', e, h'⟩ := (hs' _).mp h
  obtain ⟨e1, e2⟩ := M.op_inj e
  rw [e1, e2]
  exact h'

section wo

variable {R : V} (hR : M.IsWO R) (hfld : ∀ a, M.mem (M.op a a) R)
include hR hfld

theorem rst_fld {x s : V} (hs : M.IsRst R x s) (a : V) : M.mem (M.op a a) s ↔ M.mem a x :=
  (hs a a).trans ⟨fun h => h.2.1, fun h => ⟨hfld a, h, h⟩⟩

theorem isWO_rst {x s : V} (hs : M.IsRst R x s) : M.IsWO s := by
  refine ⟨fun a b h => ?_, fun a b c h1 h2 => ?_, fun a b h1 h2 => ?_, fun X hX => ?_⟩
  · obtain ⟨-, ha, hb⟩ := (hs a b).mp h
    exact ⟨(hs a a).mpr ⟨hfld a, ha, ha⟩, (hs b b).mpr ⟨hfld b, hb, hb⟩⟩
  · obtain ⟨h1', ha, -⟩ := (hs a b).mp h1
    obtain ⟨h2', -, hc⟩ := (hs b c).mp h2
    exact (hs a c).mpr ⟨hR.trans a b c h1' h2', ha, hc⟩
  · exact hR.antisymm a b ((hs a b).mp h1).1 ((hs b a).mp h2).1
  · obtain ⟨a, haX, has⟩ := hX
    have hax : M.mem a x := ((hs a a).mp has).2.1
    obtain ⟨Y, hY⟩ := M.exists_cap X x
    obtain ⟨b, hbY, -, hmin⟩ := hR.least Y ⟨a, (hY a).mpr ⟨haX, hax⟩, hfld a⟩
    obtain ⟨hbX, hbx⟩ := (hY b).mp hbY
    refine ⟨b, hbX, (hs b b).mpr ⟨hfld b, hbx, hbx⟩, fun c hcX hcs => ?_⟩
    have hcx : M.mem c x := ((hs c c).mp hcs).2.1
    exact (hs b c).mpr ⟨hmin c ((hY c).mpr ⟨hcX, hcx⟩) (hfld c), hbx, hcx⟩

omit hR hfld in
/-- An embedding of well-orderings as an initial segment is an injection between the
fields. -/
theorem le_of_emb {s t x y : V} (hs : M.IsWO s) (ht : M.IsWO t)
    (hx : ∀ a, M.mem (M.op a a) s ↔ M.mem a x) (hy : ∀ b, M.mem (M.op b b) t ↔ M.mem b y)
    (h : M.Emb s t) : M.Le x y := by
  obtain ⟨f, hf, htot⟩ := h
  refine ⟨f, fun u hu => ?_, fun u u' w w' hu hu' hp hp' => ⟨fun e => ?_, fun e => ?_⟩⟩
  · obtain ⟨w, hw⟩ := htot u ((hx u).mpr hu)
    exact ⟨w, (hy w).mp (hf.1 u w hw).2, hw⟩
  · subst e
    exact M.piso_fun ht hf hp hp'
  · subst e
    exact M.piso_inj hs hf hp hp'

/-- With a well-ordering of the universe, any two sets are comparable. -/
theorem wo_le_total (x y : V) : M.Le x y ∨ M.Le y x := by
  obtain ⟨s, hs⟩ := M.exists_rst R x
  obtain ⟨t, ht⟩ := M.exists_rst R y
  have hs' := M.isWO_rst hR hfld hs
  have ht' := M.isWO_rst hR hfld ht
  rcases M.emb_total hs' ht' with h | h
  · exact Or.inl (M.le_of_emb hs' ht' (M.rst_fld hR hfld hs) (M.rst_fld hR hfld ht) h)
  · exact Or.inr (M.le_of_emb ht' hs' (M.rst_fld hR hfld ht) (M.rst_fld hR hfld hs) h)

/-- With a well-ordering of the universe, every nonempty set of sets has a least member
for `≼`. -/
theorem wo_le_least (C : V) (hC : ∃ x, M.mem x C) :
    ∃ x, M.mem x C ∧ ∀ y, M.mem y C → M.Le x y := by
  obtain ⟨x1, hx1⟩ := hC
  obtain ⟨r, hr⟩ := M.exists_rst R x1
  have hr' := M.isWO_rst hR hfld hr
  obtain ⟨A, -, hA0⟩ := M.comp (σW [(1, 5), (2, 5), (3, 5), (4, 3), (5, 4), (6, 5)])
    (.and (fApp 2 19 19) (Fml.ex 1 (Fml.ex 3 (.and
      (Fml.ex 4 (.and (.mem 4 5) (.all 12 (.all 13 (Fml.iff (fApp 1 12 13)
        (.and (fApp 6 12 13) (.and (.mem 12 4) (.mem 13 4))))))))
      segOfFml))))
    19 rfl (Function.update (Function.update (Function.update (fun _ => dflt) 2 r) 5 C) 6 R)
  have hA : ∀ a, M.mem a A ↔ M.mem (M.op a a) r ∧
      ∃ s f, (∃ x, M.mem x C ∧ M.IsRst R x s) ∧ M.SegOf s r f a := by
    intro a
    rw [hA0 a]
    simp [Sat, M.sat_ex, M.sat_iff, M.sat_fApp, M.sat_segOfFml, Function.update_apply, IsRst]
  obtain ⟨s, ⟨x, hx, hsx⟩, hmin⟩ := M.wo_min hr' (fun s => ∃ x, M.mem x C ∧ M.IsRst R x s)
    (fun s ⟨x, _, hs⟩ => M.isWO_rst hR hfld hs) ⟨x1, hx1, hr⟩ A hA
  refine ⟨x, hx, fun y hy => ?_⟩
  obtain ⟨t, ht⟩ := M.exists_rst R y
  exact M.le_of_emb (M.isWO_rst hR hfld hsx) (M.isWO_rst hR hfld ht) (M.rst_fld hR hfld hsx)
    (M.rst_fld hR hfld ht) (hmin t ⟨y, hy, ht⟩)

end wo

/-- **The universe of NF has no well-ordering.** There is no set relation that is a
well-ordering (reflexive, transitive, antisymmetric, with a least element in every set that
meets its field) whose field is the whole universe. -/
theorem no_wellOrdering_univ : ¬ ∃ R, M.IsWO R ∧ ∀ a, M.mem (M.op a a) R := by
  rintro ⟨R, hR, hfld⟩
  exact M.not_wellOrdered_le ⟨M.wo_le_total hR hfld, fun C hC => M.wo_le_least hR hfld C hC⟩

end Model

end NFUCut



/-!
# Specker's theorem, part 5: NF refutes the axiom of choice

The axiom of choice is taken in the form: every set of nonempty, pairwise disjoint sets has a
choice set. From it Zermelo's argument of 1908 gives a well-ordering of the universe: choose an
element `γ(s)` from every nonempty set `s`; a *chain* is a family of sets that contains the
universe and is closed under `s ↦ s ∖ {γ(s)}` and under intersections; the members of the least
chain are the final segments of the well-ordering. By part 4 there is no such well-ordering.

Because the choice of an element lowers the type, the choice function is a set of pairs
`⟨s, {a}⟩` with `a ∈ s`.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hNF : Fact (∀ x : V, M.isSet x)]

/-- **The axiom of choice**: every set of nonempty, pairwise disjoint sets has a set that
meets each of them in exactly one element. -/
def AC : Prop :=
  ∀ X, (∀ a, M.mem a X → ∃ u, M.mem u a) →
    (∀ a b u, M.mem a X → M.mem b X → M.mem u a → M.mem u b → a = b) →
    ∃ c, ∀ a, M.mem a X → ∃ u, M.mem u a ∧ M.mem u c ∧ ∀ u', M.mem u' a → M.mem u' c → u' = u

/-- `a` is the element that `c` selects from `s`. -/
def Pick (c s a : V) : Prop := M.mem a s ∧ M.mem (M.op s (M.sing a)) c

theorem exists_fiber (s : V) : ∃ G, ∀ p, M.mem p G ↔ ∃ a, M.mem a s ∧ p = M.op s (M.sing a) := by
  obtain ⟨G, -, h⟩ := M.comp (σSp [(0, 3), (1, 1), (4, 1)])
    (Fml.ex 2 (Fml.ex 4 (.and (.mem 2 1) (.and (fS 0 4 2) (fP 1 0 1 4))))) 0 rfl
    (Function.update (fun _ => dflt) 1 s)
  refine ⟨G, fun p => ?_⟩
  rw [h p]
  simp [M.sat_ex, Sat, M.sat_fS, M.sat_fP, Function.update_apply]

theorem exists_fibers : ∃ X, ∀ G, M.mem G X ↔ ∃ s, (∃ u, M.mem u s) ∧
    ∀ p, (M.mem p G ↔ ∃ a, M.mem a s ∧ p = M.op s (M.sing a)) := by
  obtain ⟨X, -, h⟩ := M.comp (σSp [(0, 4), (1, 1), (2, 0), (3, 3), (4, 1)])
    (Fml.ex 1 (.and (Fml.ex 2 (.mem 2 1)) (.all 3 (Fml.iff (.mem 3 0)
      (Fml.ex 2 (Fml.ex 4 (.and (.mem 2 1) (.and (fS 0 4 2) (fP 1 3 1 4))))))))) 0 rfl
    (fun _ => dflt)
  refine ⟨X, fun G => ?_⟩
  rw [h G]
  simp [M.sat_ex, Sat, M.sat_iff, M.sat_fS, M.sat_fP, Function.update_apply]

/-- From the axiom of choice, a selector: a set that selects one element from every nonempty
set. -/
theorem exists_selector (hAC : M.AC) : ∃ c, ∀ s, (∃ u, M.mem u s) →
    ∃ a, M.Pick c s a ∧ ∀ a', M.Pick c s a' → a' = a := by
  obtain ⟨X, hX⟩ := M.exists_fibers
  have h1 : ∀ G, M.mem G X → ∃ p, M.mem p G := by
    intro G hG
    obtain ⟨s, ⟨u, hu⟩, hGs⟩ := (hX G).mp hG
    exact ⟨_, (hGs _).mpr ⟨u, hu, rfl⟩⟩
  have h2 : ∀ G G' p, M.mem G X → M.mem G' X → M.mem p G → M.mem p G' → G = G' := by
    intro G G' p hG hG' hp hp'
    obtain ⟨s, -, hGs⟩ := (hX G).mp hG
    obtain ⟨s', -, hGs'⟩ := (hX G').mp hG'
    obtain ⟨a, -, e⟩ := (hGs p).mp hp
    obtain ⟨a', -, e'⟩ := (hGs' p).mp hp'
    have es : s = s' := (M.op_inj (e.symm.trans e')).1
    subst es
    exact M.ext' hNF.out fun q => (hGs q).trans (hGs' q).symm
  obtain ⟨c, hc⟩ := hAC X h1 h2
  refine ⟨c, fun s hs => ?_⟩
  obtain ⟨G, hG⟩ := M.exists_fiber s
  obtain ⟨p, hpG, hpc, huniq⟩ := hc G ((hX G).mpr ⟨s, hs, hG⟩)
  obtain ⟨a, ha, e⟩ := (hG p).mp hpG
  subst e
  refine ⟨a, ⟨ha, hpc⟩, fun a' ha' => ?_⟩
  have e' := huniq _ ((hG _).mpr ⟨a', ha'.1, rfl⟩) ha'.2
  exact M.sing_inj (M.op_inj e').2

/-! ## Chains -/

/-- `s ⊆ t`. -/
def Sb (s t : V) : Prop := ∀ u, M.mem u s → M.mem u t

/-- `s' = s ∖ {a}`. -/
def IsRem (s a s' : V) : Prop := ∀ u, M.mem u s' ↔ M.mem u s ∧ u ≠ a

/-- `m = ⋂ T`. -/
def IsInter (T m : V) : Prop := ∀ u, M.mem u m ↔ ∀ t, M.mem t T → M.mem u t

/-- A chain for the selector `c`: a family of sets that contains the universe and is closed
under removing the selected element and under intersections of nonempty subfamilies. -/
def IsChn (c K : V) : Prop :=
  M.mem M.univ K ∧
    (∀ s a s', M.mem s K → M.Pick c s a → M.IsRem s a s' → M.mem s' K) ∧
    ∀ T m, (∃ t, M.mem t T) → (∀ t, M.mem t T → M.mem t K) → M.IsInter T m → M.mem m K

theorem exists_sInter (T : V) : ∃ m, M.IsInter T m := by
  obtain ⟨m, -, h⟩ := M.comp (fun i => i) (.all 1 (Fml.imp (.mem 1 2) (.mem 0 1))) 0 rfl
    (Function.update (fun _ => dflt) 2 T)
  refine ⟨m, fun u => ?_⟩
  rw [h u]
  simp [Sat, M.sat_imp, Function.update_apply]

theorem exists_K0 (c : V) : ∃ K0, ∀ s, M.mem s K0 ↔ ∀ K, M.IsChn c K → M.mem s K := by
  obtain ⟨K0, -, h⟩ := M.comp
    (σSp [(0, 1), (1, 2), (2, 4), (3, 1), (4, 1), (5, 0), (6, 1), (7, 1), (8, 0), (9, 2), (10, 1),
      (11, 1)])
    (.all 1 (Fml.imp (.and (.mem 3 1) (.and
      (.all 4 (.all 5 (.all 6 (Fml.imp (.mem 4 1) (Fml.imp
        (.and (.mem 5 4) (Fml.ex 7 (.and (fS 0 7 5) (fI 1 4 7 2))))
        (Fml.imp (.all 8 (Fml.iff (.mem 8 6) (.and (.mem 8 4) (.neg (.eq 8 5))))) (.mem 6 1)))))))
      (.all 9 (.all 10 (Fml.imp (Fml.ex 11 (.mem 11 9))
        (Fml.imp (.all 11 (Fml.imp (.mem 11 9) (.mem 11 1)))
        (Fml.imp (.all 8 (Fml.iff (.mem 8 10) (.all 11 (Fml.imp (.mem 11 9) (.mem 8 11)))))
          (.mem 10 1))))))))
      (.mem 0 1)))
    0 rfl (Function.update (Function.update (fun _ => dflt) 2 c) 3 M.univ)
  refine ⟨K0, fun s => ?_⟩
  rw [h s]
  simp [Sat, M.sat_imp, M.sat_iff, M.sat_ex, M.sat_fS, M.sat_fI, Function.update_apply, IsChn,
    Pick, IsRem, IsInter]

/-- The least chain. -/
noncomputable def K0 (c : V) : V := Classical.choose (M.exists_K0 c)

theorem mem_K0 {c s : V} : M.mem s (M.K0 c) ↔ ∀ K, M.IsChn c K → M.mem s K :=
  Classical.choose_spec (M.exists_K0 c) s

theorem K0_chn (c : V) : M.IsChn c (M.K0 c) :=
  ⟨M.mem_K0.mpr fun K hK => hK.1,
    fun s a s' hs ha hs' => M.mem_K0.mpr fun K hK => hK.2.1 s a s' (M.mem_K0.mp hs K hK) ha hs',
    fun T m hT hTK hm => M.mem_K0.mpr fun K hK =>
      hK.2.2 T m hT (fun t ht => M.mem_K0.mp (hTK t ht) K hK) hm⟩

theorem K0_min {c K s : V} (hK : M.IsChn c K) (hs : M.mem s (M.K0 c)) : M.mem s K :=
  M.mem_K0.mp hs K hK

section selector

variable {c : V}
  (hsel : ∀ s, (∃ u, M.mem u s) → ∃ a, M.Pick c s a ∧ ∀ a', M.Pick c s a' → a' = a)
include hsel

theorem pick_unique {s a b : V} (ha : M.Pick c s a) (hb : M.Pick c s b) : a = b := by
  obtain ⟨d, -, hd⟩ := hsel s ⟨a, ha.1⟩
  rw [hd a ha, hd b hb]

/-- Zermelo's key step: if `s` is comparable with every member of the least chain, then every
member of the least chain is included in `s ∖ {γ(s)}` or includes `s`. -/
theorem zermelo_key {s a s' : V} (hs : M.mem s (M.K0 c))
    (hcmp : ∀ t, M.mem t (M.K0 c) → M.Sb t s ∨ M.Sb s t) (ha : M.Pick c s a)
    (hs' : M.IsRem s a s') : ∀ t, M.mem t (M.K0 c) → M.Sb t s' ∨ M.Sb s t := by
  obtain ⟨U, -, hU0⟩ := M.comp (fun i => if i = 1 then 2 else if i = 3 then 0 else 1)
    (.and (.mem 0 1) (Fml.or (.all 3 (Fml.imp (.mem 3 0) (.mem 3 2)))
      (.all 3 (Fml.imp (.mem 3 4) (.mem 3 0))))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 (M.K0 c)) 2 s') 4 s)
  have hU : ∀ t, M.mem t U ↔ M.mem t (M.K0 c) ∧ (M.Sb t s' ∨ M.Sb s t) := by
    intro t
    rw [hU0 t]
    simp [Sat, M.sat_imp, M.sat_or, Function.update_apply, Sb]
  have hch : M.IsChn c U := by
    refine ⟨(hU _).mpr ⟨(M.K0_chn c).1, Or.inr fun u _ => M.mem_univ u⟩,
      fun t b t' ht hb ht' => ?_, fun T m hT hTU hm => ?_⟩
    · obtain ⟨htK, hor⟩ := (hU t).mp ht
      have ht'K : M.mem t' (M.K0 c) := (M.K0_chn c).2.1 t b t' htK hb ht'
      refine (hU _).mpr ⟨ht'K, ?_⟩
      rcases hor with h | h
      · exact Or.inl fun u hu => h u ((ht' u).mp hu).1
      · rcases hcmp t' ht'K with h2 | h2
        · by_cases hbs : M.mem b s
          · have hts : M.Sb t s := fun u hu => by
              by_cases e : u = b
              · rw [e]
                exact hbs
              · exact h2 u ((ht' u).mpr ⟨hu, e⟩)
            have est : t = s := M.ext' hNF.out fun u => ⟨hts u, h u⟩
            rw [est] at hb
            have eab : b = a := M.pick_unique hsel hb ha
            rw [eab, est] at ht'
            exact Or.inl fun u hu => (hs' u).mpr ((ht' u).mp hu)
          · exact Or.inr fun u hu => (ht' u).mpr ⟨h u hu, fun e => hbs (e ▸ hu)⟩
        · exact Or.inr h2
    · have hmK : M.mem m (M.K0 c) :=
        (M.K0_chn c).2.2 T m hT (fun t ht => ((hU t).mp (hTU t ht)).1) hm
      refine (hU _).mpr ⟨hmK, ?_⟩
      by_cases hex : ∃ t, M.mem t T ∧ M.Sb t s'
      · obtain ⟨t, ht, hts⟩ := hex
        exact Or.inl fun u hu => hts u ((hm u).mp hu t ht)
      · refine Or.inr fun u hu => (hm u).mpr fun t ht => ?_
        rcases ((hU t).mp (hTU t ht)).2 with h | h
        · exact absurd ⟨t, ht, h⟩ hex
        · exact h u hu
  intro t ht
  exact ((hU t).mp (M.K0_min hch ht)).2

/-- The least chain is linearly ordered by inclusion. -/
theorem K0_cmp {s : V} (hs : M.mem s (M.K0 c)) :
    ∀ t, M.mem t (M.K0 c) → M.Sb t s ∨ M.Sb s t := by
  obtain ⟨A, -, hA0⟩ := M.comp (fun i => if i = 1 then 2 else if i = 3 then 0 else 1)
    (.and (.mem 0 1) (.all 2 (Fml.imp (.mem 2 1) (Fml.or (.all 3 (Fml.imp (.mem 3 2) (.mem 3 0)))
      (.all 3 (Fml.imp (.mem 3 0) (.mem 3 2))))))) 0 rfl
    (Function.update (fun _ => dflt) 1 (M.K0 c))
  have hA : ∀ s, M.mem s A ↔
      M.mem s (M.K0 c) ∧ ∀ t, M.mem t (M.K0 c) → M.Sb t s ∨ M.Sb s t := by
    intro s
    rw [hA0 s]
    simp [Sat, M.sat_imp, M.sat_or, Function.update_apply, Sb]
  have hch : M.IsChn c A := by
    refine ⟨(hA _).mpr ⟨(M.K0_chn c).1, fun t _ => Or.inl fun u _ => M.mem_univ u⟩,
      fun s a s' hs ha hs' => ?_, fun T m hT hTA hm => ?_⟩
    · obtain ⟨hsK, hcmp⟩ := (hA s).mp hs
      have key := M.zermelo_key hsel hsK hcmp ha hs'
      refine (hA _).mpr ⟨(M.K0_chn c).2.1 s a s' hsK ha hs', fun t ht => ?_⟩
      rcases key t ht with h | h
      · exact Or.inl h
      · exact Or.inr fun u hu => h u ((hs' u).mp hu).1
    · refine (hA _).mpr ⟨(M.K0_chn c).2.2 T m hT (fun t ht => ((hA t).mp (hTA t ht)).1) hm,
        fun t ht => ?_⟩
      by_cases hall : ∀ s, M.mem s T → M.Sb t s
      · exact Or.inl fun u hu => (hm u).mpr fun s hs => hall s hs u hu
      · rw [not_forall] at hall
        obtain ⟨s, hs⟩ := hall
        rw [Classical.not_imp] at hs
        obtain ⟨hsT, hns⟩ := hs
        rcases ((hA s).mp (hTA s hsT)).2 t ht with h | h
        · exact absurd h hns
        · exact Or.inr fun u hu => h u ((hm u).mp hu s hsT)
  exact ((hA s).mp (M.K0_min hch hs)).2

/-- For every `a`, the least member of the least chain that contains `a` selects `a`. -/
theorem exists_final (a : V) : ∃ m, M.mem m (M.K0 c) ∧ M.mem a m ∧
    (∀ s, M.mem s (M.K0 c) → M.mem a s → M.Sb m s) ∧ M.Pick c m a := by
  obtain ⟨T, -, hT0⟩ := M.comp (fun i => if i = 1 then 2 else if i = 2 then 0 else 1)
    (.and (.mem 0 1) (.mem 2 0)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 (M.K0 c)) 2 a)
  have hT : ∀ s, M.mem s T ↔ M.mem s (M.K0 c) ∧ M.mem a s := by
    intro s
    rw [hT0 s]
    simp [Sat, Function.update_apply]
  obtain ⟨m, hm⟩ := M.exists_sInter T
  have hmK : M.mem m (M.K0 c) :=
    (M.K0_chn c).2.2 T m ⟨M.univ, (hT _).mpr ⟨(M.K0_chn c).1, M.mem_univ a⟩⟩
      (fun t ht => ((hT t).mp ht).1) hm
  have ham : M.mem a m := (hm a).mpr fun t ht => ((hT t).mp ht).2
  have hmin : ∀ s, M.mem s (M.K0 c) → M.mem a s → M.Sb m s :=
    fun s hs has u hu => (hm u).mp hu s ((hT s).mpr ⟨hs, has⟩)
  obtain ⟨d, hd, -⟩ := hsel m ⟨a, ham⟩
  have hda : d = a := by
    by_contra hne
    obtain ⟨m', -, hm'⟩ := M.exists_rem m d
    have hm'K : M.mem m' (M.K0 c) := (M.K0_chn c).2.1 m d m' hmK hd hm'
    have hdm' : M.mem d m' := hmin m' hm'K ((hm' a).mpr ⟨ham, fun e => hne e.symm⟩) d hd.1
    exact ((hm' d).mp hdm').2 rfl
  rw [hda] at hd
  exact ⟨m, hmK, ham, hmin, hd⟩

/-- **Zermelo's theorem**: a selector gives a well-ordering of the universe. -/
theorem zermelo_wo : ∃ R, M.IsWO R ∧ ∀ a, M.mem (M.op a a) R := by
  obtain ⟨R, -, hR0⟩ := M.comp (σSp [(0, 2), (1, 2), (4, 1)])
    (Fml.ex 2 (Fml.ex 3 (.and (fP 0 0 2 3)
      (.all 4 (Fml.imp (.mem 4 1) (Fml.imp (.mem 2 4) (.mem 3 4))))))) 0 rfl
    (Function.update (fun _ => dflt) 1 (M.K0 c))
  have hR : ∀ a b, M.mem (M.op a b) R ↔ ∀ s, M.mem s (M.K0 c) → M.mem a s → M.mem b s := by
    intro a b
    rw [hR0]
    simp only [M.sat_ex, Sat, M.sat_imp,
      M.sat_fP 0 (p := 0) (a := 2) (b := 3) (by decide) (by decide) (by decide)]
    simp only [Function.update_apply]
    simp only [reduceIte, Nat.reduceEqDiff]
    constructor
    · rintro ⟨a', b', e, h⟩
      obtain ⟨e1, e2⟩ := M.op_inj e
      rw [e1, e2]
      exact h
    · exact fun h => ⟨a, b, rfl, h⟩
  have hrefl : ∀ a, M.mem (M.op a a) R := fun a => (hR a a).mpr fun s _ h => h
  refine ⟨R, ⟨fun a b _ => ⟨hrefl a, hrefl b⟩, fun a b d h1 h2 => ?_, fun a b h1 h2 => ?_,
    fun X hX => ?_⟩, hrefl⟩
  · exact (hR a d).mpr fun s hs has => (hR b d).mp h2 s hs ((hR a b).mp h1 s hs has)
  · obtain ⟨ma, hmaK, hama, hmina, hpa⟩ := M.exists_final hsel a
    obtain ⟨mb, hmbK, hbmb, hminb, hpb⟩ := M.exists_final hsel b
    have hb_ma : M.mem b ma := (hR a b).mp h1 ma hmaK hama
    have ha_mb : M.mem a mb := (hR b a).mp h2 mb hmbK hbmb
    have e : ma = mb :=
      M.ext' hNF.out fun u => ⟨hmina mb hmbK ha_mb u, hminb ma hmaK hb_ma u⟩
    rw [e] at hpa
    exact M.pick_unique hsel hpa hpb
  · obtain ⟨x0, hx0, -⟩ := hX
    obtain ⟨T, -, hT0⟩ := M.comp (fun i => if i = 1 then 2 else if i = 3 then 0 else 1)
      (.and (.mem 0 1) (.all 3 (Fml.imp (.mem 3 2) (.mem 3 0)))) 0 rfl
      (Function.update (Function.update (fun _ => dflt) 1 (M.K0 c)) 2 X)
    have hT : ∀ s, M.mem s T ↔ M.mem s (M.K0 c) ∧ M.Sb X s := by
      intro s
      rw [hT0 s]
      simp [Sat, M.sat_imp, Function.update_apply, Sb]
    obtain ⟨m, hm⟩ := M.exists_sInter T
    have hmK : M.mem m (M.K0 c) :=
      (M.K0_chn c).2.2 T m ⟨M.univ, (hT _).mpr ⟨(M.K0_chn c).1, fun u _ => M.mem_univ u⟩⟩
        (fun t ht => ((hT t).mp ht).1) hm
    have hXm : M.Sb X m := fun u hu => (hm u).mpr fun t ht => ((hT t).mp ht).2 u hu
    obtain ⟨d, hd, -⟩ := hsel m ⟨x0, hXm x0 hx0⟩
    obtain ⟨m', -, hm'⟩ := M.exists_rem m d
    have hm'K : M.mem m' (M.K0 c) := (M.K0_chn c).2.1 m d m' hmK hd hm'
    have hdX : M.mem d X := by
      by_contra hno
      have hXm' : M.Sb X m' := fun u hu => (hm' u).mpr ⟨hXm u hu, fun e => hno (e ▸ hu)⟩
      have hdm' : M.mem d m' := (hm d).mp hd.1 m' ((hT m').mpr ⟨hm'K, hXm'⟩)
      exact ((hm' d).mp hdm').2 rfl
    refine ⟨d, hdX, hrefl d, fun b hb _ => (hR d b).mpr fun s hs hds => ?_⟩
    rcases M.zermelo_key hsel hmK (M.K0_cmp hsel hmK) hd hm' s hs with h | h
    · exact absurd rfl ((hm' d).mp (h d hds)).2
    · exact h b (hXm b hb)

end selector

/-- The axiom of choice gives a well-ordering of the universe. -/
theorem ac_wellOrdering (hAC : M.AC) : ∃ R, M.IsWO R ∧ ∀ a, M.mem (M.op a a) R := by
  obtain ⟨c, hsel⟩ := M.exists_selector hAC
  exact M.zermelo_wo hsel

/-- **NF refutes the axiom of choice.** In a model of NF, some set of nonempty, pairwise
disjoint sets has no choice set. -/
theorem nf_not_choice : ¬ M.AC := fun h => M.no_wellOrdering_univ (M.ac_wellOrdering h)

end Model

end NFUCut



/-!
# Specker's theorem, part 6: the statements for `IsNF`

`ConNF.NF.IsNF V mem` says that `(V, mem)` satisfies extensionality and every instance of
stratified comprehension, with formulas in de Bruijn form. Such a structure is a model of NFU,
in the sense of `NFUCut.Model`, in which every object is a set. So the theorems of the
previous parts hold in every model of NF, and NF interprets NFU + Infinity by the identity.
-/

namespace NFUCut

open ConNF.NF (Fm IsNF)

/-- All the names that occur in a formula, free or bound. -/
def Fml.names : Fml → List ℕ
  | .mem a b => [a, b]
  | .eq a b => [a, b]
  | .set a => [a]
  | .neg φ => φ.names
  | .and φ ψ => φ.names ++ ψ.names
  | .all a φ => a :: φ.names

/-- The translation of a formula with named variables into de Bruijn form. The list `ctx`
gives the name of each index. "Is a set" becomes a true formula. -/
def trF (σ : ℕ → ℕ) : List ℕ → Fml → Fm
  | ctx, .mem a b => .mem (ctx.idxOf a) (ctx.idxOf b)
  | ctx, .eq a b => .eq (ctx.idxOf a) (ctx.idxOf b)
  | ctx, .set a => .eq (ctx.idxOf a) (ctx.idxOf a)
  | ctx, .neg φ => .neg (trF σ ctx φ)
  | ctx, .and φ ψ => .and (trF σ ctx φ) (trF σ ctx ψ)
  | ctx, .all a φ => .all (σ a) (trF σ (a :: ctx) φ)

theorem sat_trF {V : Type} (mem : V → V → Prop) (σ : ℕ → ℕ) :
    ∀ (φ : Fml) (ctx : List ℕ) (env : List V) (ρ : ℕ → V),
      (∀ n ∈ φ.names, n ∈ ctx) → (∀ n ∈ ctx, env[ctx.idxOf n]? = some (ρ n)) →
      (ConNF.NF.Sat mem (trF σ ctx φ) env ↔ Sat mem (fun _ => True) φ ρ) := by
  intro φ
  induction φ with
  | mem a b =>
    intro ctx env ρ hn hag
    have ha := hag a (hn a (by simp [Fml.names]))
    have hb := hag b (hn b (by simp [Fml.names]))
    simp [trF, ConNF.NF.Sat, Sat, ha, hb]
  | eq a b =>
    intro ctx env ρ hn hag
    have ha := hag a (hn a (by simp [Fml.names]))
    have hb := hag b (hn b (by simp [Fml.names]))
    simp only [trF, ConNF.NF.Sat, Sat, ha, hb]
    exact ⟨fun ⟨u, v, e1, e2, e3⟩ => by
        rw [Option.some.inj e1, Option.some.inj e2]
        exact e3, fun e => ⟨ρ a, ρ b, rfl, rfl, e⟩⟩
  | set a =>
    intro ctx env ρ hn hag
    have ha := hag a (hn a (by simp [Fml.names]))
    simp [trF, ConNF.NF.Sat, Sat, ha]
  | neg φ ih =>
    intro ctx env ρ hn hag
    simp only [trF, ConNF.NF.Sat, Sat]
    rw [ih ctx env ρ hn hag]
  | and φ ψ ih1 ih2 =>
    intro ctx env ρ hn hag
    simp only [trF, ConNF.NF.Sat, Sat]
    rw [ih1 ctx env ρ (fun n h => hn n (by simp [Fml.names, h])) hag,
      ih2 ctx env ρ (fun n h => hn n (by simp [Fml.names, h])) hag]
  | all a φ ih =>
    intro ctx env ρ hn hag
    simp only [trF, ConNF.NF.Sat, Sat]
    refine forall_congr' fun v => ?_
    refine ih (a :: ctx) (v :: env) (Function.update ρ a v)
      (fun n h => List.mem_cons_of_mem _ (hn n (by simp [Fml.names, h]))) ?_
    intro n hmem
    by_cases e : n = a
    · subst e
      simp
    · have hctx : n ∈ ctx := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h e
        · exact h
      rw [List.idxOf_cons_ne _ (Ne.symm e), Function.update_of_ne e]
      simpa using hag n hctx

theorem strat_trF (σ : ℕ → ℕ) : ∀ (φ : Fml) (ctx : List ℕ), (∀ n ∈ φ.names, n ∈ ctx) →
    φ.strat σ = true → ConNF.NF.Strat (ctx.map σ) (trF σ ctx φ) := by
  intro φ
  induction φ with
  | mem a b =>
    intro ctx hn hs
    have ha : (ctx.map σ)[ctx.idxOf a]? = some (σ a) := by
      rw [List.getElem?_map, List.getElem?_idxOf (hn a (by simp [Fml.names]))]
      rfl
    have hb : (ctx.map σ)[ctx.idxOf b]? = some (σ b) := by
      rw [List.getElem?_map, List.getElem?_idxOf (hn b (by simp [Fml.names]))]
      rfl
    have e : σ b = σ a + 1 := by simpa [Fml.strat] using hs
    exact ⟨σ a, ha, by rw [hb, e]⟩
  | eq a b =>
    intro ctx hn hs
    have ha : (ctx.map σ)[ctx.idxOf a]? = some (σ a) := by
      rw [List.getElem?_map, List.getElem?_idxOf (hn a (by simp [Fml.names]))]
      rfl
    have hb : (ctx.map σ)[ctx.idxOf b]? = some (σ b) := by
      rw [List.getElem?_map, List.getElem?_idxOf (hn b (by simp [Fml.names]))]
      rfl
    have e : σ a = σ b := by simpa [Fml.strat] using hs
    exact ⟨σ a, ha, by rw [hb, e]⟩
  | set a =>
    intro ctx hn hs
    have ha : (ctx.map σ)[ctx.idxOf a]? = some (σ a) := by
      rw [List.getElem?_map, List.getElem?_idxOf (hn a (by simp [Fml.names]))]
      rfl
    exact ⟨σ a, ha, ha⟩
  | neg φ ih =>
    intro ctx hn hs
    exact ih ctx hn hs
  | and φ ψ ih1 ih2 =>
    intro ctx hn hs
    have hs' : φ.strat σ = true ∧ ψ.strat σ = true := by simpa [Fml.strat] using hs
    exact ⟨ih1 ctx (fun n h => hn n (by simp [Fml.names, h])) hs'.1,
      ih2 ctx (fun n h => hn n (by simp [Fml.names, h])) hs'.2⟩
  | all a φ ih =>
    intro ctx hn hs
    exact ih (a :: ctx) (fun n h => List.mem_cons_of_mem _ (hn n (by simp [Fml.names, h]))) hs

/-- **A model of NF is a model of NFU in which every object is a set.** -/
def modelOfNF {V : Type} {mem : V → V → Prop} (h : IsNF V mem) : Model V where
  mem := mem
  isSet := fun _ => True
  isSet_of_mem := fun _ => trivial
  ext := fun _ _ hz => h.ext _ _ hz
  comp := fun σ φ x hφ ρ => by
    have hn : ∀ n ∈ φ.names, n ∈ x :: φ.names := fun n hn => List.mem_cons_of_mem _ hn
    obtain ⟨y, hy⟩ := h.comprehension (σ x) (φ.names.map σ) (trF σ (x :: φ.names) φ)
      (strat_trF σ φ (x :: φ.names) hn hφ) (φ.names.map ρ) (by simp)
    refine ⟨y, trivial, fun a => ?_⟩
    rw [hy a]
    refine sat_trF mem σ φ (x :: φ.names) (a :: φ.names.map ρ) (Function.update ρ x a) hn ?_
    intro n hmem
    by_cases e : n = x
    · subst e
      simp
    · have hctx : n ∈ φ.names := by
        rcases List.mem_cons.mp hmem with h' | h'
        · exact absurd h' e
        · exact h'
      rw [List.idxOf_cons_ne _ (Ne.symm e), Function.update_of_ne e]
      simp [List.getElem?_map, List.getElem?_idxOf hctx]

theorem modelOfNF_mem {V : Type} {mem : V → V → Prop} (h : IsNF V mem) :
    (modelOfNF h).mem = mem := rfl

theorem modelOfNF_isSet {V : Type} {mem : V → V → Prop} (h : IsNF V mem) (x : V) :
    (modelOfNF h).isSet x := trivial

section

variable {V : Type} {mem : V → V → Prop}

theorem _root_.ConNF.NF.IsNF.nonempty (h : IsNF V mem) : Nonempty V := by
  obtain ⟨y, -⟩ := h.exists_univ
  exact ⟨y⟩

/-- **NF proves Infinity.** In a model of NF the universe belongs to no natural number
(Frege's natural numbers, as defined in `NFUCut.Model`). -/
theorem _root_.ConNF.NF.IsNF.infinity (h : IsNF V mem) [Nonempty V] : (modelOfNF h).Infinity :=
  haveI : Fact (∀ x : V, (modelOfNF h).isSet x) := ⟨fun _ => trivial⟩
  (modelOfNF h).nf_infinity

/-- **NF proves Infinity**, stated with membership only: the universe is not finite in
Kuratowski's sense. There is a family of sets that contains every empty set and is closed
under adjoining one element, but does not contain a universal set. -/
theorem _root_.ConNF.NF.IsNF.univ_not_finite (h : IsNF V mem) :
    ¬ ∀ F : V, (∀ e, (∀ u, ¬ mem u e) → mem e F) →
      (∀ s s' b, mem s F → (∀ u, mem u s' ↔ mem u s ∨ u = b) → mem s' F) →
      ∀ v, (∀ u, mem u v) → mem v F := by
  have := h.nonempty
  have : Fact (∀ x : V, (modelOfNF h).isSet x) := ⟨fun _ => trivial⟩
  let M := modelOfNF h
  intro hfin
  have hF := hfin (M.sUnion M.nat) (fun e he => ?_) (fun s s' b hs hs' => ?_) M.univ M.mem_univ
  · obtain ⟨k, hk, hu⟩ := M.mem_sUnion.mp hF
    exact M.nf_infinity k hk hu
  · have e1 : e = M.emp := M.eq_emp trivial he
    rw [e1]
    exact M.mem_sUnion.mpr ⟨M.zero, M.zero_mem_nat, M.mem_zero.mpr rfl⟩
  · obtain ⟨k, hk, hsk⟩ := M.mem_sUnion.mp hs
    have e1 : s' = M.adj s b := M.eq_adj_iff.mp hs'
    obtain ⟨-, k', hk', hsk'⟩ := M.fin_adj b ⟨trivial, k, hk, hsk⟩
    rw [e1]
    exact M.mem_sUnion.mpr ⟨k', hk', hsk'⟩

/-- **NF refutes the axiom of choice**, stated with membership only: in a model of NF it is
not the case that every set of nonempty, pairwise disjoint sets has a set that meets each of
them in exactly one element. -/
theorem _root_.ConNF.NF.IsNF.not_choice (h : IsNF V mem) :
    ¬ ∀ X : V, (∀ a, mem a X → ∃ u, mem u a) →
      (∀ a b u, mem a X → mem b X → mem u a → mem u b → a = b) →
      ∃ c, ∀ a, mem a X → ∃ u, mem u a ∧ mem u c ∧ ∀ u', mem u' a → mem u' c → u' = u := by
  have := h.nonempty
  have : Fact (∀ x : V, (modelOfNF h).isSet x) := ⟨fun _ => trivial⟩
  exact (modelOfNF h).nf_not_choice

/-- **NF interprets NFU + Infinity**, by the identity: every model of NF, with every object
declared a set, is a model of NFU in which Infinity holds. -/
theorem nf_interprets_nfu_inf (h : IsNF V mem) :
    ∃ (_ : Nonempty V) (M : Model V), M.mem = mem ∧ (∀ x, M.isSet x) ∧ M.Infinity :=
  ⟨h.nonempty, modelOfNF h, rfl, fun _ => trivial, haveI := h.nonempty; h.infinity⟩

end

end NFUCut

