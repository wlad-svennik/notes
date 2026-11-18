import NFMac

set_option autoImplicit false

/-!
# Functions in a model of `𝗡𝗙`: every object as a function

In a model `V` of `𝗡𝗙` this file defines a relation `AppR f x y` ("`f` applied to `x` is `y`")
that is stratified with `f` one type above `x` and `y`, total and single-valued, extensional,
and such that every total single-valued relation that is a set of pairs is `AppR f` for some
`f`. The steps:

* `Sg`: a one-to-one map `σ` of the universe into itself that preserves types and misses one
  object: the successor on the finite ordinals `Hin.InOm` of `NFMac.lean`, the identity
  elsewhere. This is where Specker's theorem is used.
* `Pr p x y`: Quine's ordered pair `p = {σ"a : a ∈ x} ∪ {σ"b ∪ {0} : b ∈ y}`, which has the
  type of `x` and `y`.
* `Fn F`: `F` is a set of pairs that is total and single-valued. `Ap0 F x y`: the pair of `x`
  and `y` is in `F`.
* `Chi s F`: `F` is the characteristic function of `s`. It is a one-to-one map of the universe
  into the set of functions.
* `J f F`: the bijection between the universe and the set of functions given by the proof of
  the Cantor–Schröder–Bernstein theorem from `Chi` and the inclusion. `InC` is the closure of
  the set of non-functions under `Chi`.
* `AppR f x y`: `Ap0 (J f) x y`.
-/

namespace FFL.FirstOrder.SetTheory

namespace NFFn

open Hin

section defs

variable {V : Type} [SetStructure V]

/-- `y = σ x`: the successor of `x` if `x` is a finite ordinal, and `x` otherwise. -/
def Sg (x y : V) : Prop := (InOm x ∧ Succ x y) ∨ (¬InOm x ∧ y = x)

/-- `w` is the image of `a` under `σ`. -/
def Im1 (w a : V) : Prop := ∀ v, v ∈ w ↔ ∃ u, u ∈ a ∧ Sg u v

/-- `w` is the image of `b` under `σ`, with zero added. -/
def Im2 (w b : V) : Prop := ∀ v, v ∈ w ↔ (∃ u, u ∈ b ∧ Sg u v) ∨ IsZero v

/-- `p` is Quine's ordered pair of `x` and `y`. -/
def Pr (p x y : V) : Prop := ∀ w, w ∈ p ↔ (∃ a, a ∈ x ∧ Im1 w a) ∨ (∃ b, b ∈ y ∧ Im2 w b)

/-- The pair of `x` and `y` is in `F`. -/
def Ap0 (F x y : V) : Prop := ∃ p, p ∈ F ∧ Pr p x y

/-- `F` is a function defined on the whole universe: a set of pairs, total and single-valued. -/
def Fn (F : V) : Prop :=
  (∀ p, p ∈ F → ∃ x y, Pr p x y) ∧ (∀ x, ∃ y, Ap0 F x y) ∧
    ∀ x y y', Ap0 F x y → Ap0 F x y' → y = y'

/-- `t` is the universal set, used as the truth value `⊤`. -/
def IsTT (t : V) : Prop := ∀ z, z ∈ t

/-- `t` is the empty set, used as the truth value `⊥`. -/
def IsFF (t : V) : Prop := ∀ z, z ∉ t

/-- `F` is the characteristic function of `s`. -/
def Chi (s F : V) : Prop :=
  ∀ p, p ∈ F ↔ ∃ z, (z ∈ s ∧ ∃ t, IsTT t ∧ Pr p z t) ∨ (z ∉ s ∧ ∃ t, IsFF t ∧ Pr p z t)

/-- `X` contains the objects that are not functions and is closed under `Chi`. -/
def Closed (X : V) : Prop := (∀ F, ¬Fn F → F ∈ X) ∧ ∀ s, s ∈ X → ∀ F, Chi s F → F ∈ X

/-- `x` is in the closure of the set of non-functions under `Chi`. -/
def InC (x : V) : Prop := ∀ X : V, Closed X → x ∈ X

/-- The bijection between the universe and the set of functions. -/
def J (f F : V) : Prop := (InC f ∧ Chi f F) ∨ (¬InC f ∧ F = f)

/-- **Application**: `f` applied to `x` is `y`. -/
def AppR (f x y : V) : Prop := ∃ F, J f F ∧ Ap0 F x y

/-- The equality test: `y` is `⊤` if `a = b` and `⊥` otherwise. -/
def EqtR (a b y : V) : Prop := (a = b ∧ IsTT y) ∨ (¬a = b ∧ IsFF y)

end defs

section sdefs

def sgD : SDef ![6, 6] (fun _ _ v ↦ Sg (v 0) (v 1)) :=
  (((inOmD.comp ![0] 0).and (succD.comp ![0, 1] 0)).or
    (((inOmD.comp ![0] 0).not).and (SDef.eq 1 0))).congr fun _ _ _ => Iff.rfl

def im1D : SDef ![7, 7] (fun _ _ v ↦ Im1 (v 0) (v 1)) :=
  (SDef.all 6 ((SDef.mem 0 1).iff (SDef.ex 6 ((SDef.mem 0 3).and (sgD.comp ![0, 1] 0))))).congr
    fun _ _ _ => Iff.rfl

def im2D : SDef ![7, 7] (fun _ _ v ↦ Im2 (v 0) (v 1)) :=
  (SDef.all 6 ((SDef.mem 0 1).iff ((SDef.ex 6 ((SDef.mem 0 3).and (sgD.comp ![0, 1] 0))).or
    (isZeroD.comp ![0] 0)))).congr fun _ _ _ => Iff.rfl

def prD : SDef ![8, 8, 8] (fun _ _ v ↦ Pr (v 0) (v 1) (v 2)) :=
  (SDef.all 7 ((SDef.mem 0 1).iff ((SDef.ex 7 ((SDef.mem 0 3).and (im1D.comp ![1, 0] 0))).or
    (SDef.ex 7 ((SDef.mem 0 4).and (im2D.comp ![1, 0] 0)))))).congr fun _ _ _ => Iff.rfl

def ap0D : SDef ![9, 8, 8] (fun _ _ v ↦ Ap0 (v 0) (v 1) (v 2)) :=
  (SDef.ex 8 ((SDef.mem 0 1).and (prD.comp ![0, 2, 3] 0))).congr fun _ _ _ => Iff.rfl

def fnD : SDef ![9] (fun _ _ v ↦ Fn (v 0)) :=
  ((SDef.all 8 ((SDef.mem 0 1).imp (SDef.ex 8 (SDef.ex 8 (prD.comp ![2, 1, 0] 0))))).and
    ((SDef.all 8 (SDef.ex 8 (ap0D.comp ![2, 1, 0] 0))).and
      (SDef.all 8 (SDef.all 8 (SDef.all 8 ((ap0D.comp ![3, 2, 1] 0).imp
        ((ap0D.comp ![3, 2, 0] 0).imp (SDef.eq 1 0)))))))).congr fun _ _ _ => Iff.rfl

def ttD : SDef ![1] (fun _ _ v ↦ IsTT (v 0)) :=
  (SDef.all 0 (SDef.mem 0 1)).congr fun _ _ _ => Iff.rfl

def ffD : SDef ![1] (fun _ _ v ↦ IsFF (v 0)) :=
  (SDef.all 0 ((SDef.mem 0 1).not)).congr fun _ _ _ => Iff.rfl

def chiD : SDef ![9, 9] (fun _ _ v ↦ Chi (v 0) (v 1)) :=
  (SDef.all 8 ((SDef.mem 0 2).iff (SDef.ex 8
    (((SDef.mem 0 2).and (SDef.ex 8 ((ttD.comp ![0] 7).and (prD.comp ![2, 1, 0] 0)))).or
      (((SDef.mem 0 2).not).and
        (SDef.ex 8 ((ffD.comp ![0] 7).and (prD.comp ![2, 1, 0] 0)))))))).congr
    fun _ _ _ => Iff.rfl

def closedD : SDef ![10] (fun _ _ v ↦ Closed (v 0)) :=
  ((SDef.all 9 (((fnD.comp ![0] 0).not).imp (SDef.mem 0 1))).and
    (SDef.all 9 ((SDef.mem 0 1).imp (SDef.all 9 ((chiD.comp ![1, 0] 0).imp
      (SDef.mem 0 2)))))).congr fun _ _ _ => Iff.rfl

def inCD : SDef ![9] (fun _ _ v ↦ InC (v 0)) :=
  (SDef.all 10 ((closedD.comp ![0] 0).imp (SDef.mem 1 0))).congr fun _ _ _ => Iff.rfl

def jD : SDef ![9, 9] (fun _ _ v ↦ J (v 0) (v 1)) :=
  (((inCD.comp ![0] 0).and (chiD.comp ![0, 1] 0)).or
    (((inCD.comp ![0] 0).not).and (SDef.eq 1 0))).congr fun _ _ _ => Iff.rfl

def appD : SDef ![9, 8, 8] (fun _ _ v ↦ AppR (v 0) (v 1) (v 2)) :=
  (SDef.ex 9 ((jD.comp ![1, 0] 0).and (ap0D.comp ![0, 2, 3] 0))).congr fun _ _ _ => Iff.rfl

def eqtD : SDef ![1, 1, 1] (fun _ _ v ↦ EqtR (v 0) (v 1) (v 2)) :=
  (((SDef.eq 0 1).and (ttD.comp ![2] 0)).or
    (((SDef.eq 0 1).not).and (ffD.comp ![2] 0))).congr fun _ _ _ => Iff.rfl

end sdefs

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-! ### The map `σ` -/

theorem exists_upair (a b : V) : ∃ S : V, ∀ x, x ∈ S ↔ x = a ∨ x = b :=
  ((SDef.eq (τ := ![0, 0, 0]) 0 1).or (SDef.eq 0 2)).comprehension ![a, b]

theorem succ_inj {y y' w : V} (h : Succ y w) (h' : Succ y' w) : y = y' := by
  by_contra hne
  have h1 : EE y y' := ((h'.2.2 y).mp ((h.2.2 y).mpr (Or.inr rfl))).resolve_right hne
  have h2 : EE y' y :=
    ((h.2.2 y').mp ((h'.2.2 y').mpr (Or.inr rfl))).resolve_right (fun e => hne e.symm)
  obtain ⟨S, hS⟩ := exists_upair y y'
  obtain ⟨x, hx, -, hmin⟩ := ee_wf S ⟨y, (hS y).mpr (Or.inl rfl), h.1⟩
  rcases (hS x).mp hx with e | e
  · rw [e] at hmin
    exact hmin y' ((hS y').mpr (Or.inr rfl)) h2
  · rw [e] at hmin
    exact hmin y ((hS y).mpr (Or.inl rfl)) h1

theorem sg_total (x : V) : ∃ y, Sg x y := by
  by_cases hx : InOm x
  · obtain ⟨w, hw, _⟩ := om_succ_exists hx
    exact ⟨w, Or.inl ⟨hx, hw⟩⟩
  · exact ⟨x, Or.inr ⟨hx, rfl⟩⟩

theorem sg_fun {x y y' : V} (h : Sg x y) (h' : Sg x y') : y = y' := by
  rcases h with ⟨hx, hs⟩ | ⟨hx, e⟩ <;> rcases h' with ⟨hx', hs'⟩ | ⟨hx', e'⟩
  · exact succ_unique hs hs'
  · exact absurd hx hx'
  · exact absurd hx' hx
  · rw [e, e']

theorem sg_inj {x x' y : V} (h : Sg x y) (h' : Sg x' y) : x = x' := by
  rcases h with ⟨hx, hs⟩ | ⟨hx, e⟩ <;> rcases h' with ⟨hx', hs'⟩ | ⟨hx', e'⟩
  · exact succ_inj hs hs'
  · exfalso
    rw [e'] at hs
    exact hx' (om_succ hx hs)
  · exfalso
    rw [e] at hs'
    exact hx (om_succ hx' hs')
  · exact e.symm.trans e'

theorem sg_ne_zero {x y : V} (h : Sg x y) : ¬IsZero y := by
  intro hz
  rcases h with ⟨hx, hs⟩ | ⟨hx, e⟩
  · exact hz.2 x ((hs.2.2 x).mpr (Or.inr rfl))
  · rw [e] at hz
    exact hx (om_zero hz)

/-! ### Quine's ordered pair -/

theorem exists_im1 (a : V) : ∃ w, Im1 w a :=
  (SDef.ex (τ := ![6, 7]) 6 ((SDef.mem 0 2).and (sgD.comp ![0, 1] 0))).comprehension ![a]

theorem exists_im2 (b : V) : ∃ w, Im2 w b :=
  ((SDef.ex (τ := ![6, 7]) 6 ((SDef.mem 0 2).and (sgD.comp ![0, 1] 0))).or
    (isZeroD.comp ![0] 0)).comprehension ![b]

theorem im1_inj {w a a' : V} (h : Im1 w a) (h' : Im1 w a') : a = a' := by
  have key : ∀ {a a' : V}, Im1 w a → Im1 w a' → ∀ u, u ∈ a → u ∈ a' := by
    intro a a' h h' u hu
    obtain ⟨v, hv⟩ := sg_total u
    obtain ⟨u', hu', hv'⟩ := (h' v).mp ((h v).mpr ⟨u, hu, hv⟩)
    rw [sg_inj hv hv']
    exact hu'
  exact nf_ext fun u => ⟨key h h' u, key h' h u⟩

theorem im2_inj {w b b' : V} (h : Im2 w b) (h' : Im2 w b') : b = b' := by
  have key : ∀ {b b' : V}, Im2 w b → Im2 w b' → ∀ u, u ∈ b → u ∈ b' := by
    intro b b' h h' u hu
    obtain ⟨v, hv⟩ := sg_total u
    obtain ⟨u', hu', hv'⟩ :=
      ((h' v).mp ((h v).mpr (Or.inl ⟨u, hu, hv⟩))).resolve_right (sg_ne_zero hv)
    rw [sg_inj hv hv']
    exact hu'
  exact nf_ext fun u => ⟨key h h' u, key h' h u⟩

theorem im12 {w a b : V} (h1 : Im1 w a) (h2 : Im2 w b) : False := by
  obtain ⟨z, hz⟩ := exists_zero (V := V)
  obtain ⟨u, _, hu⟩ := (h1 z).mp ((h2 z).mpr (Or.inr hz))
  exact sg_ne_zero hu hz

theorem exists_pr (x y : V) : ∃ p, Pr p x y :=
  ((SDef.ex (τ := ![7, 8, 8]) 7 ((SDef.mem 0 2).and (im1D.comp ![1, 0] 0))).or
    (SDef.ex 7 ((SDef.mem 0 3).and (im2D.comp ![1, 0] 0)))).comprehension ![x, y]

theorem pr_unique {p p' x y : V} (h : Pr p x y) (h' : Pr p' x y) : p = p' :=
  nf_ext fun w => (h w).trans (h' w).symm

theorem pr_inj {p x y x' y' : V} (h : Pr p x y) (h' : Pr p x' y') : x = x' ∧ y = y' := by
  have k1 : ∀ {x y x' y' : V}, Pr p x y → Pr p x' y' → ∀ a, a ∈ x → a ∈ x' := by
    intro x y x' y' h h' a ha
    obtain ⟨w, hw⟩ := exists_im1 a
    rcases (h' w).mp ((h w).mpr (Or.inl ⟨a, ha, hw⟩)) with ⟨a', ha', hw'⟩ | ⟨b, _, hw'⟩
    · rw [im1_inj hw hw']
      exact ha'
    · exact (im12 hw hw').elim
  have k2 : ∀ {x y x' y' : V}, Pr p x y → Pr p x' y' → ∀ b, b ∈ y → b ∈ y' := by
    intro x y x' y' h h' b hb
    obtain ⟨w, hw⟩ := exists_im2 b
    rcases (h' w).mp ((h w).mpr (Or.inr ⟨b, hb, hw⟩)) with ⟨a, _, hw'⟩ | ⟨b', hb', hw'⟩
    · exact (im12 hw' hw).elim
    · rw [im2_inj hw hw']
      exact hb'
  exact ⟨nf_ext fun a => ⟨k1 h h' a, k1 h' h a⟩, nf_ext fun b => ⟨k2 h h' b, k2 h' h b⟩⟩

/-! ### Truth values -/

theorem exists_tt : ∃ t : V, IsTT t := by
  obtain ⟨t, ht⟩ := (SDef.eq (τ := ![0]) 0 0).comprehension (![] : Fin 0 → V)
  exact ⟨t, fun z => (ht z).mpr rfl⟩

theorem exists_ff : ∃ t : V, IsFF t := exists_empty

theorem tt_unique {t t' : V} (h : IsTT t) (h' : IsTT t') : t = t' :=
  nf_ext fun z => ⟨fun _ => h' z, fun _ => h z⟩

theorem ff_unique {t t' : V} (h : IsFF t) (h' : IsFF t') : t = t' :=
  nf_ext fun z => ⟨fun hz => absurd hz (h z), fun hz => absurd hz (h' z)⟩

omit hT in
theorem tt_ne_ff {t f : V} (ht : IsTT t) (hf : IsFF f) : t ≠ f := fun e => by
  rw [e] at ht
  exact hf (Classical.arbitrary V) (ht (Classical.arbitrary V))

/-! ### Functions -/

theorem fn_eq {F G : V} (hF : Fn F) (hG : Fn G) (h : ∀ x y, Ap0 F x y → Ap0 G x y) : F = G := by
  refine nf_ext fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨x, y, hpr⟩ := hF.1 p hp
    obtain ⟨p', hp', hpr'⟩ := h x y ⟨p, hp, hpr⟩
    rw [pr_unique hpr hpr']
    exact hp'
  · obtain ⟨x, y, hpr⟩ := hG.1 p hp
    obtain ⟨y', hy'⟩ := hF.2.1 x
    have e := hG.2.2 x y y' ⟨p, hp, hpr⟩ (h x y' hy')
    obtain ⟨p', hp', hpr'⟩ := hy'
    rw [← e] at hpr'
    rw [pr_unique hpr hpr']
    exact hp'

/-- A set of pairs given by a total single-valued relation is a function. -/
theorem fn_of_set {F : V} {G : V → V → Prop} (hF : ∀ p, p ∈ F ↔ ∃ x y, Pr p x y ∧ G x y)
    (htot : ∀ x, ∃ y, G x y) (hfun : ∀ x y y', G x y → G x y' → y = y') :
    Fn F ∧ ∀ x y, Ap0 F x y ↔ G x y := by
  have key : ∀ x y, Ap0 F x y ↔ G x y := fun x y => ⟨fun ⟨p, hp, hpr⟩ => by
      obtain ⟨x', y', hpr', hG⟩ := (hF p).mp hp
      obtain ⟨e1, e2⟩ := pr_inj hpr hpr'
      rw [e1, e2]
      exact hG, fun hG => by
      obtain ⟨p, hpr⟩ := exists_pr x y
      exact ⟨p, (hF p).mpr ⟨x, y, hpr, hG⟩, hpr⟩⟩
  exact ⟨⟨fun p hp => let ⟨x, y, hpr, _⟩ := (hF p).mp hp; ⟨x, y, hpr⟩,
    fun x => let ⟨y, hy⟩ := htot x; ⟨y, (key x y).mpr hy⟩,
    fun x y y' h h' => hfun x y y' ((key x y).mp h) ((key x y').mp h')⟩, key⟩

/-! ### Characteristic functions -/

theorem exists_chi (s : V) : ∃ F, Chi s F :=
  (SDef.ex (τ := ![8, 9]) 8
    (((SDef.mem 0 2).and (SDef.ex 8 ((ttD.comp ![0] 7).and (prD.comp ![2, 1, 0] 0)))).or
      (((SDef.mem 0 2).not).and
        (SDef.ex 8 ((ffD.comp ![0] 7).and (prD.comp ![2, 1, 0] 0)))))).comprehension ![s]

theorem chi_spec {s F : V} (h : Chi s F) :
    Fn F ∧ ∀ x y, Ap0 F x y ↔ (x ∈ s ∧ IsTT y) ∨ (x ∉ s ∧ IsFF y) := by
  refine fn_of_set (G := fun x y => (x ∈ s ∧ IsTT y) ∨ (x ∉ s ∧ IsFF y))
    (fun p => (h p).trans ⟨?_, ?_⟩) ?_ ?_
  · rintro ⟨z, ⟨hz, t, ht, hp⟩ | ⟨hz, t, ht, hp⟩⟩
    · exact ⟨z, t, hp, Or.inl ⟨hz, ht⟩⟩
    · exact ⟨z, t, hp, Or.inr ⟨hz, ht⟩⟩
  · rintro ⟨x, y, hp, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · exact ⟨x, Or.inl ⟨hx, y, hy, hp⟩⟩
    · exact ⟨x, Or.inr ⟨hx, y, hy, hp⟩⟩
  · intro x
    by_cases hx : x ∈ s
    · obtain ⟨t, ht⟩ := exists_tt (V := V)
      exact ⟨t, Or.inl ⟨hx, ht⟩⟩
    · obtain ⟨t, ht⟩ := exists_ff (V := V)
      exact ⟨t, Or.inr ⟨hx, ht⟩⟩
  · rintro x y y' (⟨hx, hy⟩ | ⟨hx, hy⟩) (⟨hx', hy'⟩ | ⟨hx', hy'⟩)
    · exact tt_unique hy hy'
    · exact absurd hx hx'
    · exact absurd hx' hx
    · exact ff_unique hy hy'

theorem chi_unique {s F F' : V} (h : Chi s F) (h' : Chi s F') : F = F' :=
  nf_ext fun p => (h p).trans (h' p).symm

theorem chi_inj {s s' F : V} (h : Chi s F) (h' : Chi s' F) : s = s' := by
  obtain ⟨t, ht⟩ := exists_tt (V := V)
  have key : ∀ {s s' : V}, Chi s F → Chi s' F → ∀ z, z ∈ s → z ∈ s' := by
    intro s s' h h' z hz
    have h1 := ((chi_spec h).2 z t).mpr (Or.inl ⟨hz, ht⟩)
    rcases ((chi_spec h').2 z t).mp h1 with ⟨hz', _⟩ | ⟨_, hf⟩
    · exact hz'
    · exact absurd rfl (tt_ne_ff ht hf)
  exact nf_ext fun z => ⟨key h h' z, key h' h z⟩

/-! ### The bijection between the universe and the set of functions -/

omit [Nonempty V] hT in
theorem inC_of_not_fn {F : V} (h : ¬Fn F) : InC F := fun _ hX => hX.1 F h

omit [Nonempty V] hT in
theorem inC_chi {s F : V} (hs : InC s) (h : Chi s F) : InC F :=
  fun X hX => hX.2 s (hs X hX) F h

/-- A function in the closure is a characteristic function of a member of the closure. -/
theorem inC_inv {F : V} (hC : InC F) (hF : Fn F) : ∃ s, InC s ∧ Chi s F := by
  by_contra hno
  obtain ⟨C', hC'⟩ :=
    ((inCD.comp (τ' := ![9, 9]) ![0] 0).and ((SDef.eq 0 1).not)).comprehension ![F]
  have hC'' : ∀ x, x ∈ C' ↔ InC x ∧ ¬x = F := hC'
  have hcl : Closed C' := ⟨fun G hG => (hC'' G).mpr ⟨inC_of_not_fn hG, fun e => hG (by
      rw [e]; exact hF)⟩, fun s hs G hG => (hC'' G).mpr ⟨inC_chi ((hC'' s).mp hs).1 hG,
      fun e => hno ⟨s, ((hC'' s).mp hs).1, by rw [← e]; exact hG⟩⟩⟩
  exact ((hC'' F).mp (hC C' hcl)).2 rfl

theorem j_total (f : V) : ∃ F, J f F := by
  by_cases h : InC f
  · obtain ⟨F, hF⟩ := exists_chi f
    exact ⟨F, Or.inl ⟨h, hF⟩⟩
  · exact ⟨f, Or.inr ⟨h, rfl⟩⟩

theorem j_fn {f F : V} (h : J f F) : Fn F := by
  rcases h with ⟨_, hc⟩ | ⟨hn, e⟩
  · exact (chi_spec hc).1
  · rw [e]
    by_contra hf
    exact hn (inC_of_not_fn hf)

theorem j_fun {f F F' : V} (h : J f F) (h' : J f F') : F = F' := by
  rcases h with ⟨hc, hx⟩ | ⟨hn, e⟩ <;> rcases h' with ⟨hc', hx'⟩ | ⟨hn', e'⟩
  · exact chi_unique hx hx'
  · exact absurd hc hn'
  · exact absurd hc' hn
  · rw [e, e']

theorem j_inj {f f' F : V} (h : J f F) (h' : J f' F) : f = f' := by
  rcases h with ⟨hc, hx⟩ | ⟨hn, e⟩ <;> rcases h' with ⟨hc', hx'⟩ | ⟨hn', e'⟩
  · exact chi_inj hx hx'
  · exfalso
    rw [e'] at hx
    exact hn' (inC_chi hc hx)
  · exfalso
    rw [e] at hx'
    exact hn (inC_chi hc' hx')
  · exact e.symm.trans e'

theorem j_surj {F : V} (hF : Fn F) : ∃ f, J f F := by
  by_cases h : InC F
  · obtain ⟨s, hs, hc⟩ := inC_inv h hF
    exact ⟨s, Or.inl ⟨hs, hc⟩⟩
  · exact ⟨F, Or.inr ⟨h, rfl⟩⟩

/-! ### Application -/

theorem app_total (f x : V) : ∃ y, AppR f x y := by
  obtain ⟨F, hF⟩ := j_total f
  obtain ⟨y, hy⟩ := (j_fn hF).2.1 x
  exact ⟨y, F, hF, hy⟩

theorem app_fun {f x y y' : V} (h : AppR f x y) (h' : AppR f x y') : y = y' := by
  obtain ⟨F, hF, hy⟩ := h
  obtain ⟨F', hF', hy'⟩ := h'
  rw [← j_fun hF hF'] at hy'
  exact (j_fn hF).2.2 x y y' hy hy'

/-- **Extensionality.** -/
theorem app_ext {f g : V} (h : ∀ x y, AppR f x y → AppR g x y) : f = g := by
  obtain ⟨F, hF⟩ := j_total f
  obtain ⟨G, hG⟩ := j_total g
  have e : F = G := fn_eq (j_fn hF) (j_fn hG) fun x y hxy => by
    obtain ⟨G', hG', hy⟩ := h x y ⟨F, hF, hxy⟩
    rw [j_fun hG hG']
    exact hy
  rw [e] at hF
  exact j_inj hF hG

/-- **Abstraction.** A set of pairs given by a total single-valued relation `G` is the graph of
`AppR f` for some `f`. -/
theorem app_of_graph {F : V} {G : V → V → Prop} (hF : ∀ p, p ∈ F ↔ ∃ x y, Pr p x y ∧ G x y)
    (htot : ∀ x, ∃ y, G x y) (hfun : ∀ x y y', G x y → G x y' → y = y') :
    ∃ f, ∀ x y, AppR f x y ↔ G x y := by
  obtain ⟨hFn, key⟩ := fn_of_set hF htot hfun
  obtain ⟨f, hf⟩ := j_surj hFn
  exact ⟨f, fun x y => ⟨fun ⟨F', hF', h⟩ => (key x y).mp (by rw [j_fun hf hF']; exact h),
    fun h => ⟨F, hf, (key x y).mpr h⟩⟩⟩

/-! ### The equality test -/

theorem eqt_total (a b : V) : ∃ y, EqtR a b y := by
  by_cases h : a = b
  · obtain ⟨t, ht⟩ := exists_tt (V := V)
    exact ⟨t, Or.inl ⟨h, ht⟩⟩
  · obtain ⟨t, ht⟩ := exists_ff (V := V)
    exact ⟨t, Or.inr ⟨h, ht⟩⟩

theorem eqt_fun {a b y y' : V} (h : EqtR a b y) (h' : EqtR a b y') : y = y' := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases h' with ⟨hx', hy'⟩ | ⟨hx', hy'⟩
  · exact tt_unique hy hy'
  · exact absurd hx hx'
  · exact absurd hx' hx
  · exact ff_unique hy hy'

end model

end NFFn

end FFL.FirstOrder.SetTheory
