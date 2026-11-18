import MHHull
import MHSep

set_option autoImplicit false

/-!
# Condensation: a bound for the constructible subsets of a level

Inside a model `V` of `𝗠𝗛`. Let `x₀` be a constructible subset of the level at `ν`.

* A hull `N` of `Lev ν ∪ {Lev ν, x₀}` inside a level at a limit ordinal: `N` is closed under the
  eight operations over the levels that are its members, under passing from a set to the level
  at which it appears and to the components of its least definition, under the successor of
  levels, under pairs, and under passing to the least member of a set (`HullData`).
* `N` is an image of a set of codes that depends on `ν` only, so the collapse axiom gives one
  transitive set `T`, depending on `ν` only, that contains the collapse of `N`.
* The collapse of `N` is the identity on `x₀`, and it maps the members of `N` in a level onto a
  level (`main_ind`). So `x₀` is a member of the level at the ordinals of `T` (`bound_exists`).
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

open Semiformula

section defs

variable {V : Type} [SetStructure V]

/-- `A` is the level of `f` at `γ`. -/
def LevAt (f γ A : V) : Prop :=
  ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A', A' ∈ w ∧ ∃ w', w' ∈ d ∧
    ∃ lt, lt ∈ w' ∧ (IsOp q γ d ∧ (IsOp d A' lt ∧ A' = A))

/-- `x` is the set defined over the level `L` of `f` at `γ` by the parameters in the pairs
`p₁` and `p₂`. -/
def OpAt (f γ L p₁ p₂ x : V) : Prop :=
  ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ d ∧
    ∃ lt, lt ∈ w' ∧ (IsOp q γ d ∧ (IsOp d A lt ∧ (A = L ∧
      ∃ s, s ∈ A ∧ ∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ ∃ c, c ∈ A ∧
        (IsOp p₁ s a ∧ (IsOp p₂ b c ∧ IsD A lt s a b c x)))))

/-- `(s, a, b, c)` is the least definition of `y` over the level of `f` at `β`. -/
def LdAt (f β y s a b c : V) : Prop :=
  ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ d ∧
    ∃ lt, lt ∈ w' ∧ (IsOp q β d ∧ (IsOp d A lt ∧ (s ∈ A ∧ (a ∈ A ∧ (b ∈ A ∧ (c ∈ A ∧
      LeastD A lt s a b c y))))))

/-- **The function of the hull**, of four arguments, the first of which is a numeral that
selects the case. -/
def GH (y₀ y₁ y₂ y₃ x F D lt' W : V) : Prop :=
  (IsNum 0 y₀ ∧ IsOp x y₁ y₂) ∨
  ((IsNum 1 y₀ ∧ ∃ β, β ∈ D ∧ (RkAt F β y₁ ∧ LevAt F β x)) ∨
  ((IsNum 2 y₀ ∧ ∃ γ, γ ∈ D ∧ ∃ γ', γ' ∈ D ∧ (SuccR γ' γ ∧ (LevAt F γ y₁ ∧ LevAt F γ' x))) ∨
  ((IsNum 3 y₀ ∧ ∃ γ, γ ∈ D ∧ OpAt F γ y₁ y₂ y₃ x) ∨
  ((IsNum 4 y₀ ∧ ∃ β, β ∈ D ∧ (RkAt F β y₁ ∧ ∃ a, a ∈ W ∧ ∃ b, b ∈ W ∧ ∃ c, c ∈ W ∧
      LdAt F β y₁ x a b c)) ∨
  ((IsNum 5 y₀ ∧ ∃ β, β ∈ D ∧ (RkAt F β y₁ ∧ ∃ a, a ∈ W ∧ ∃ b, b ∈ W ∧ ∃ c, c ∈ W ∧
      LdAt F β y₁ a x b c)) ∨
  ((IsNum 6 y₀ ∧ ∃ β, β ∈ D ∧ (RkAt F β y₁ ∧ ∃ a, a ∈ W ∧ ∃ b, b ∈ W ∧ ∃ c, c ∈ W ∧
      LdAt F β y₁ a b x c)) ∨
  ((IsNum 7 y₀ ∧ ∃ β, β ∈ D ∧ (RkAt F β y₁ ∧ ∃ a, a ∈ W ∧ ∃ b, b ∈ W ∧ ∃ c, c ∈ W ∧
      LdAt F β y₁ a b c x)) ∨
  (IsNum 8 y₀ ∧ (x ∈ y₁ ∧ ∀ z, z ∈ y₁ → ¬Pr lt' z x)))))))))

end defs

def levAtB : BDef (k := 3) (fun V _ v ↦ LevAt (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0
    ((isOpB.comp ![6, 8, 4]).and ((isOpB.comp ![4, 2, 0]).and
      (BDef.eq 2 9)))))))))).congr fun _ _ _ => Iff.rfl

def opAtB : BDef (k := 6) (fun V _ v ↦ OpAt (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0
    ((isOpB.comp ![6, 8, 4]).and ((isOpB.comp ![4, 2, 0]).and ((BDef.eq 2 9).and
      (BDef.bex 2 (BDef.bex 3 (BDef.bex 4 (BDef.bex 5
        ((isOpB.comp ![14, 3, 2]).and ((isOpB.comp ![15, 1, 0]).and
          (isDB.comp ![6, 4, 3, 2, 1, 0, 16]))))))))))))))))).congr fun _ _ _ => Iff.rfl

def ldAtB : BDef (k := 7) (fun V _ v ↦ LdAt (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0
    ((isOpB.comp ![6, 8, 4]).and ((isOpB.comp ![4, 2, 0]).and ((BDef.mem 10 2).and
      ((BDef.mem 11 2).and ((BDef.mem 12 2).and ((BDef.mem 13 2).and
        (leastDB.comp ![2, 0, 10, 11, 12, 13, 9])))))))))))))).congr fun _ _ _ => Iff.rfl

def ghB : BDef (k := 9) (fun V _ v ↦ GH (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  ((((isNumB 0).comp ![0]).and (isOpB.comp ![4, 1, 2])).or
  ((((isNumB 1).comp ![0]).and (BDef.bex 6 ((rkAtB.comp ![6, 0, 2]).and
      (levAtB.comp ![6, 0, 5])))).or
  ((((isNumB 2).comp ![0]).and (BDef.bex 6 (BDef.bex 7 ((succB.comp ![0, 1]).and
      ((levAtB.comp ![7, 1, 3]).and (levAtB.comp ![7, 0, 6])))))).or
  ((((isNumB 3).comp ![0]).and (BDef.bex 6 (opAtB.comp ![6, 0, 2, 3, 4, 5]))).or
  ((((isNumB 4).comp ![0]).and (BDef.bex 6 ((rkAtB.comp ![6, 0, 2]).and
      (BDef.bex 9 (BDef.bex 10 (BDef.bex 11 (ldAtB.comp ![9, 3, 5, 8, 2, 1, 0]))))))).or
  ((((isNumB 5).comp ![0]).and (BDef.bex 6 ((rkAtB.comp ![6, 0, 2]).and
      (BDef.bex 9 (BDef.bex 10 (BDef.bex 11 (ldAtB.comp ![9, 3, 5, 2, 8, 1, 0]))))))).or
  ((((isNumB 6).comp ![0]).and (BDef.bex 6 ((rkAtB.comp ![6, 0, 2]).and
      (BDef.bex 9 (BDef.bex 10 (BDef.bex 11 (ldAtB.comp ![9, 3, 5, 2, 1, 8, 0]))))))).or
  ((((isNumB 7).comp ![0]).and (BDef.bex 6 ((rkAtB.comp ![6, 0, 2]).and
      (BDef.bex 9 (BDef.bex 10 (BDef.bex 11 (ldAtB.comp ![9, 3, 5, 2, 1, 0, 8]))))))).or
  (((isNumB 8).comp ![0]).and ((BDef.mem 4 1).and
      (BDef.ball 1 (prB.comp ![8, 0, 5]).not))))))))))).congr fun _ _ _ => Iff.rfl

/-- The condition that defines the function of the hull as a set of pairs. -/
def gSetB : BDef (k := 5) (fun V _ v ↦ ∃ y₀, y₀ ∈ v 1 ∧ ∃ y₁, y₁ ∈ v 1 ∧ ∃ y₂, y₂ ∈ v 1 ∧
    ∃ y₃, y₃ ∈ v 1 ∧ ∃ x, x ∈ v 1 ∧ (IsQ5 (v 0) y₀ y₁ y₂ y₃ x ∧
      GH y₀ y₁ y₂ y₃ x (v 2) (v 3) (v 4) (v 1))) :=
  (BDef.bex 1 (BDef.bex 2 (BDef.bex 3 (BDef.bex 4 (BDef.bex 5
    ((isQ5B.comp ![5, 4, 3, 2, 1, 0]).and
      (ghB.comp ![4, 3, 2, 1, 0, 7, 8, 9, 6]))))))).congr fun _ _ _ => Iff.rfl

/-- The condition that defines the generators as a set of pairs. -/
def genB : BDef (k := 4) (fun V _ v ↦ (v 0 ∈ v 2 ∧ v 1 = v 0) ∨ (v 0 = v 2 ∧ v 1 = v 3)) :=
  (((BDef.mem 0 2).and (BDef.eq 1 0)).or ((BDef.eq 0 2).and (BDef.eq 1 3))).congr
    fun _ _ _ => Iff.rfl

section setup

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem levAt_iff {f γ A : V} : LevAt f γ A ↔ ∃ lt, Pr f γ (kp A lt) :=
  exAt_iff.trans ⟨fun ⟨_, lt, h, e⟩ => ⟨lt, e ▸ h⟩, fun ⟨lt, h⟩ => ⟨A, lt, h, rfl⟩⟩

theorem opAt_iff {f γ L p₁ p₂ x : V} : OpAt f γ L p₁ p₂ x ↔ ∃ A lt, Pr f γ (kp A lt) ∧
    (A = L ∧ ∃ s, s ∈ A ∧ ∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ ∃ c, c ∈ A ∧
      (IsOp p₁ s a ∧ (IsOp p₂ b c ∧ IsD A lt s a b c x))) := exAt_iff

theorem ldAt_iff {f β y s a b c : V} : LdAt f β y s a b c ↔ ∃ A lt, Pr f β (kp A lt) ∧
    (s ∈ A ∧ (a ∈ A ∧ (b ∈ A ∧ (c ∈ A ∧ LeastD A lt s a b c y)))) := exAt_iff

theorem levAt_lev {F δ γ A : V} (hδ : Ord δ) (hF : IsHier F δ) (hγ : γ ∈ sc δ) :
    LevAt F γ A ↔ A = Lev γ := by
  rw [levAt_iff]
  constructor
  · rintro ⟨lt, h⟩
    exact (hier_lev_eq hδ hF hγ h).1
  · intro h
    exact ⟨LtS γ, by rw [h]; exact hier_lev hδ hF hγ⟩

theorem lev_inj {γ γ' : V} (hγ : Ord γ) (hγ' : Ord γ') (h : Lev γ = Lev γ') : γ = γ' := by
  have h1 : RkL γ' (Lev γ) := by rw [h]; exact rkL_lev hγ'
  exact rkL_unique (rkL_lev hγ) h1

/-- The data: a big ordinal `ν`, a limit ordinal `δ'` above it with the sequence `F` of its
levels, and a member `x₀` of the level at `δ'` that is a subset of the level at `ν`. -/
structure Setup (ν δ' F x₀ : V) : Prop where
  big : Big ν
  lim : Lim δ'
  lt : ν ∈ δ'
  hier : IsHier F δ'
  mem : x₀ ∈ Lev δ'
  sub : ∀ z, z ∈ x₀ → z ∈ Lev ν

namespace Setup

variable {ν δ' F x₀ : V} (su : Setup ν δ' F x₀)

include su

theorem ord : Ord δ' := su.lim.1

theorem inD {γ : V} (h : γ ∈ δ') : γ ∈ sc δ' := mem_sc.mpr (Or.inr h)

theorem levAt {γ A : V} (h : γ ∈ δ') : LevAt F γ A ↔ A = Lev γ :=
  levAt_lev su.ord su.hier (su.inD h)

theorem rkAt {β a : V} (h : β ∈ δ') : RkAt F β a ↔ RkL β a :=
  rkAt_lev su.ord su.hier (su.inD h)

theorem scn_mem {γ : V} (h : γ ∈ δ') : ∀ k, scn k γ ∈ δ'
  | 0 => h
  | k + 1 => su.lim.2.2 _ (scn_mem h k)

/-- A big level below `δ'` that contains `a`. -/
theorem level_of {a : V} (ha : a ∈ Lev δ') : ∃ γ, γ ∈ δ' ∧ Big γ ∧ a ∈ Lev γ := by
  obtain ⟨β, hβ, hr⟩ := rkL_exists su.ord ha
  have hsβ : sc β ∈ δ' := su.lim.2.2 β hβ
  have haβ : a ∈ Lev (sc β) := inDef_mem hr.1 hr.2.1
  rcases ord_tri (ord_sc hr.1) su.big.1 with h | h | h
  · exact ⟨ν, su.lt, su.big, lev_mono su.big.1 h a haβ⟩
  · exact ⟨ν, su.lt, su.big, h ▸ haβ⟩
  · exact ⟨sc β, hsβ, ⟨ord_sc hr.1, fun n hn => (ord_sc hr.1).1 ν h n (su.big.2 n hn)⟩, haβ⟩

theorem level_of2 {a b : V} (ha : a ∈ Lev δ') (hb : b ∈ Lev δ') :
    ∃ γ, γ ∈ δ' ∧ Big γ ∧ a ∈ Lev γ ∧ b ∈ Lev γ := by
  obtain ⟨γ₁, h₁, g₁, a₁⟩ := su.level_of ha
  obtain ⟨γ₂, h₂, g₂, a₂⟩ := su.level_of hb
  rcases ord_tri g₁.1 g₂.1 with h | h | h
  · exact ⟨γ₂, h₂, g₂, lev_mono g₂.1 h a a₁, a₂⟩
  · exact ⟨γ₂, h₂, g₂, h ▸ a₁, a₂⟩
  · exact ⟨γ₁, h₁, g₁, a₁, lev_mono g₁.1 h b a₂⟩

theorem kp_mem {a b : V} (ha : a ∈ Lev δ') (hb : b ∈ Lev δ') : kp a b ∈ Lev δ' := by
  obtain ⟨γ, hγ, hg, h1, h2⟩ := su.level_of2 ha hb
  exact lev_mono su.ord (su.scn_mem hγ 4) _ (kp_mem_lev hg h1 h2)

theorem rk_un {β β' y : V} (hβ : β ∈ sc δ') (hβ' : β' ∈ sc δ') (h : RkAt F β y)
    (h' : RkAt F β' y) : β = β' :=
  rkL_unique ((rkAt_lev su.ord su.hier hβ).mp h) ((rkAt_lev su.ord su.hier hβ').mp h')

theorem lev_un {γ γ' y : V} (hγ : γ ∈ sc δ') (hγ' : γ' ∈ sc δ') (h : LevAt F γ y)
    (h' : LevAt F γ' y) : γ = γ' :=
  lev_inj (ord_mem (ord_sc su.ord) hγ) (ord_mem (ord_sc su.ord) hγ')
    (((levAt_lev su.ord su.hier hγ).mp h).symm.trans ((levAt_lev su.ord su.hier hγ').mp h'))

theorem ld_un {β y s a b c s' a' b' c' : V} (hβ : β ∈ sc δ') (h : LdAt F β y s a b c)
    (h' : LdAt F β y s' a' b' c') : s = s' ∧ a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨A, lt, hpr, hs, ha, hb, hc, hL⟩ := ldAt_iff.mp h
  obtain ⟨A', lt', hpr', hs', ha', hb', hc', hL'⟩ := ldAt_iff.mp h'
  obtain ⟨rfl, rfl⟩ := hier_lev_eq su.ord su.hier hβ hpr
  obtain ⟨rfl, rfl⟩ := hier_lev_eq su.ord su.hier hβ hpr'
  have hO := ord_mem (ord_sc su.ord) hβ
  exact leastD_unique hO (wol hO) hs ha hb hc hs' ha' hb' hc' hL hL'

/-- **The function of the hull has at most one value.** -/
theorem gh_fun {y₀ y₁ y₂ y₃ x x' : V} (hy₁ : y₁ ∈ Lev δ')
    (h : GH y₀ y₁ y₂ y₃ x F (sc δ') (LtS δ') (Lev δ'))
    (h' : GH y₀ y₁ y₂ y₃ x' F (sc δ') (LtS δ') (Lev δ')) : x = x' := by
  have hδ := su.ord
  have hF := su.hier
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ <;>
  rcases h' with ⟨n', h'⟩ | ⟨n', h'⟩ | ⟨n', h'⟩ | ⟨n', h'⟩ | ⟨n', h'⟩ | ⟨n', h'⟩ | ⟨n', h'⟩ |
    ⟨n', h'⟩ | ⟨n', h'⟩ <;>
  first
    | exact absurd (nm_inj (((isNum_iff _ _).mp n).symm.trans ((isNum_iff _ _).mp n')))
        (by decide)
    | skip
  · exact (isOp_iff.mp h).trans (isOp_iff.mp h').symm
  · obtain ⟨β, hβ, hr, hl⟩ := h
    obtain ⟨β', hβ', hr', hl'⟩ := h'
    have e := su.rk_un hβ hβ' hr hr'
    subst e
    exact ((levAt_lev hδ hF hβ).mp hl).trans ((levAt_lev hδ hF hβ).mp hl').symm
  · obtain ⟨γ, hγ, γ', hγ', hs, hl, hlx⟩ := h
    obtain ⟨γ₂, hγ₂, γ₂', hγ₂', hs₂, hl₂, hlx₂⟩ := h'
    have e := su.lev_un hγ hγ₂ hl hl₂
    subst e
    have e' : γ' = γ₂' := (succR_iff_sc.mp hs).trans (succR_iff_sc.mp hs₂).symm
    subst e'
    exact ((levAt_lev hδ hF hγ').mp hlx).trans ((levAt_lev hδ hF hγ').mp hlx₂).symm
  · obtain ⟨γ, hγ, hop⟩ := h
    obtain ⟨γ₂, hγ₂, hop₂⟩ := h'
    obtain ⟨A, lt, hpr, eA, s, -, a, -, b, -, c, -, o1, o2, hD⟩ := opAt_iff.mp hop
    obtain ⟨A₂, lt₂, hpr₂, eA₂, s₂, -, a₂, -, b₂, -, c₂, -, o1', o2', hD₂⟩ := opAt_iff.mp hop₂
    have e := su.lev_un hγ hγ₂ (levAt_iff.mpr ⟨lt, eA ▸ hpr⟩) (levAt_iff.mpr ⟨lt₂, eA₂ ▸ hpr₂⟩)
    subst e
    obtain ⟨e1, e2⟩ := hier_fun hF hpr hpr₂
    obtain ⟨e3, e4⟩ := op_inj o1 o1'
    obtain ⟨e5, e6⟩ := op_inj o2 o2'
    subst e1 e2 e3 e4 e5 e6
    exact mem_ext (isD_ext hD hD₂)
  · obtain ⟨β, hβ, hr, a, -, b, -, c, -, hl⟩ := h
    obtain ⟨β', hβ', hr', a', -, b', -, c', -, hl'⟩ := h'
    have e := su.rk_un hβ hβ' hr hr'
    subst e
    exact (su.ld_un hβ hl hl').1
  · obtain ⟨β, hβ, hr, a, -, b, -, c, -, hl⟩ := h
    obtain ⟨β', hβ', hr', a', -, b', -, c', -, hl'⟩ := h'
    have e := su.rk_un hβ hβ' hr hr'
    subst e
    exact (su.ld_un hβ hl hl').2.1
  · obtain ⟨β, hβ, hr, a, -, b, -, c, -, hl⟩ := h
    obtain ⟨β', hβ', hr', a', -, b', -, c', -, hl'⟩ := h'
    have e := su.rk_un hβ hβ' hr hr'
    subst e
    exact (su.ld_un hβ hl hl').2.2.1
  · obtain ⟨β, hβ, hr, a, -, b, -, c, -, hl⟩ := h
    obtain ⟨β', hβ', hr', a', -, b', -, c', -, hl'⟩ := h'
    have e := su.rk_un hβ hβ' hr hr'
    subst e
    exact (su.ld_un hβ hl hl').2.2.2
  · obtain ⟨hx, hmin⟩ := h
    obtain ⟨hx', hmin'⟩ := h'
    have hxW := lev_tr hδ y₁ hy₁ x hx
    have hxW' := lev_tr hδ y₁ hy₁ x' hx'
    rcases wol_tot hδ (wol hδ) x hxW x' hxW' with h1 | h1 | h1
    · exact absurd h1 (hmin' x hx)
    · exact h1
    · exact absurd h1 (hmin x' hx')

end Setup

/-- The function of the hull, as a set of pairs. -/
noncomputable def gSet (W F D lt' : V) : V :=
  sepB (k := 4) gSetB (prodS (prodS W (prodS W (prodS W W))) W) ![W, F, D, lt']

theorem ap4_gSet {W F D lt' y₀ y₁ y₂ y₃ x : V} :
    Ap4 (gSet W F D lt') y₀ y₁ y₂ y₃ x ↔
      y₀ ∈ W ∧ (y₁ ∈ W ∧ (y₂ ∈ W ∧ (y₃ ∈ W ∧ (x ∈ W ∧ GH y₀ y₁ y₂ y₃ x F D lt' W)))) := by
  have hg : ∀ e, e ∈ gSet W F D lt' ↔ e ∈ prodS (prodS W (prodS W (prodS W W))) W ∧
      ∃ z₀, z₀ ∈ W ∧ ∃ z₁, z₁ ∈ W ∧ ∃ z₂, z₂ ∈ W ∧ ∃ z₃, z₃ ∈ W ∧ ∃ x', x' ∈ W ∧
        (IsQ5 e z₀ z₁ z₂ z₃ x' ∧ GH z₀ z₁ z₂ z₃ x' F D lt' W) := fun e => mem_sepB _ _ _ e
  constructor
  · rintro ⟨e, he, hq⟩
    obtain ⟨-, z₀, hz₀, z₁, hz₁, z₂, hz₂, z₃, hz₃, x', hx', hq', hG⟩ := (hg e).mp he
    have e1 := (isQ5_iff.mp hq).symm.trans (isQ5_iff.mp hq')
    obtain ⟨e2, e3⟩ := kp_inj e1
    obtain ⟨e4, e5⟩ := kp_inj e2
    obtain ⟨e6, e7⟩ := kp_inj e5
    obtain ⟨e8, e9⟩ := kp_inj e7
    rw [e3, e4, e6, e8, e9]
    exact ⟨hz₀, hz₁, hz₂, hz₃, hx', hG⟩
  · rintro ⟨h₀, h₁, h₂, h₃, hx, hG⟩
    refine ⟨kp (kp y₀ (kp y₁ (kp y₂ y₃))) x, (hg _).mpr ⟨?_, y₀, h₀, y₁, h₁, y₂, h₂, y₃, h₃, x,
      hx, isQ5_iff.mpr rfl, hG⟩, isQ5_iff.mpr rfl⟩
    exact mem_prodS.mpr ⟨_, mem_prodS.mpr ⟨y₀, h₀, _, mem_prodS.mpr ⟨y₁, h₁, _,
      mem_prodS.mpr ⟨y₂, h₂, y₃, h₃, rfl⟩, rfl⟩, rfl⟩, x, hx, rfl⟩

/-- The generators, as a set of pairs: the members of `M₁` are sent to themselves, and `M₁` is
sent to `x₀`. -/
noncomputable def genS (M₁ x₀ W : V) : V := relB (k := 2) genB (sc M₁) W ![M₁, x₀]

theorem pr_genS {M₁ x₀ W a x : V} : Pr (genS M₁ x₀ W) a x ↔
    a ∈ sc M₁ ∧ x ∈ W ∧ ((a ∈ M₁ ∧ x = a) ∨ (a = M₁ ∧ x = x₀)) := pr_relB _ _ _ _ a x

/-- **A hull**: a set of members of the level at `δ'` that contains the members of the level at
`ν`, that level and `x₀`, and is closed under the function of the hull. -/
structure HullData (ν δ' F x₀ N : V) : Prop where
  su : Setup ν δ' F x₀
  sub : ∀ a, a ∈ N → a ∈ Lev δ'
  gen1 : ∀ a, a ∈ Lev ν → a ∈ N
  gen2 : Lev ν ∈ N
  gen3 : x₀ ∈ N
  clo : ∀ y₀ y₁ y₂ y₃ x, y₀ ∈ N → y₁ ∈ N → y₂ ∈ N → y₃ ∈ N → x ∈ Lev δ' →
    GH y₀ y₁ y₂ y₃ x F (sc δ') (LtS δ') (Lev δ') → x ∈ N

/-- **The hull exists**, and the set given by the collapse axiom for the codes, which depends
on `ν` only, is a set as in the collapse axiom for the hull. -/
theorem exists_hull {ν δ' F x₀ T : V} (su : Setup ν δ' F x₀)
    (hT : HCat T (HCd (sc (sc (Lev ν))))) : ∃ N, HullData ν δ' F x₀ N ∧ HCat T N := by
  obtain ⟨N, Vl, hsub, hgen, hclo, hN, hfun⟩ := hull_exists (W := Lev δ')
    (G₀ := sc (sc (Lev ν))) (gen := genS (sc (Lev ν)) x₀ (Lev δ'))
    (g := gSet (Lev δ') F (sc δ') (LtS δ'))
    (fun a x x' h h' => by
      obtain ⟨-, -, h⟩ := pr_genS.mp h
      obtain ⟨-, -, h'⟩ := pr_genS.mp h'
      rcases h with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases h' with ⟨h2, e2⟩ | ⟨h2, e2⟩
      · rw [e1, e2]
      · rw [h2] at h1; exact absurd h1 (mem_irrefl _)
      · rw [h1] at h2; exact absurd h2 (mem_irrefl _)
      · rw [e1, e2])
    (fun y₀ y₁ y₂ y₃ x x' h h' => by
      obtain ⟨-, hy₁, -, -, -, hG⟩ := ap4_gSet.mp h
      obtain ⟨-, -, -, -, -, hG'⟩ := ap4_gSet.mp h'
      exact su.gh_fun hy₁ hG hG')
  have hW : ∀ a, a ∈ Lev ν → a ∈ Lev δ' := lev_mono su.ord su.lt
  refine ⟨N, ⟨su, hsub, fun a ha => ?_, ?_, ?_,
    fun y₀ y₁ y₂ y₃ x h₀ h₁ h₂ h₃ hx hG => ?_⟩, hcat_image hT hN hfun⟩
  · have h1 : a ∈ sc (sc (Lev ν)) := mem_sc.mpr (Or.inr (mem_sc.mpr (Or.inr ha)))
    exact hgen a a h1 (hW a ha)
      (pr_genS.mpr ⟨h1, hW a ha, Or.inl ⟨mem_sc.mpr (Or.inr ha), rfl⟩⟩)
  · have h1 : Lev ν ∈ sc (sc (Lev ν)) := mem_sc.mpr (Or.inr (self_mem_sc _))
    exact hgen _ _ h1 (lev_mem su.ord su.lt)
      (pr_genS.mpr ⟨h1, lev_mem su.ord su.lt, Or.inl ⟨self_mem_sc _, rfl⟩⟩)
  · exact hgen _ _ (self_mem_sc _) su.mem (pr_genS.mpr ⟨self_mem_sc _, su.mem, Or.inr ⟨rfl, rfl⟩⟩)
  · exact hclo y₀ y₁ y₂ y₃ x h₀ h₁ h₂ h₃ hx
      (ap4_gSet.mpr ⟨hsub _ h₀, hsub _ h₁, hsub _ h₂, hsub _ h₃, hx, hG⟩)

namespace HullData

variable {ν δ' F x₀ N : V} (hd : HullData ν δ' F x₀ N)

include hd

theorem nm_mem (k : ℕ) : (nm k : V) ∈ N := hd.gen1 _ (nm_mem_lev hd.su.big k)

theorem kp_mem {a b : V} (ha : a ∈ N) (hb : b ∈ N) : kp a b ∈ N :=
  hd.clo (nm 0) a b a (kp a b) (hd.nm_mem 0) ha hb ha (hd.su.kp_mem (hd.sub a ha) (hd.sub b hb))
    (Or.inl ⟨isNum_nm 0, isOp_kp a b⟩)

theorem rk_mem {a β : V} (ha : a ∈ N) (hr : RkL β a) : β ∈ δ' ∧ Lev β ∈ N := by
  have hβ : β ∈ δ' := (rkL_mem hr hd.su.ord).mp (hd.sub a ha)
  exact ⟨hβ, hd.clo (nm 1) a a a (Lev β) (hd.nm_mem 1) ha ha ha (lev_mem hd.su.ord hβ)
    (Or.inr (Or.inl ⟨isNum_nm 1, β, hd.su.inD hβ, (hd.su.rkAt hβ).mpr hr,
      (hd.su.levAt hβ).mpr rfl⟩))⟩

theorem succ_mem {γ : V} (hγ : γ ∈ δ') (h : Lev γ ∈ N) : Lev (sc γ) ∈ N := by
  have hs : sc γ ∈ δ' := hd.su.lim.2.2 γ hγ
  exact hd.clo (nm 2) (Lev γ) (Lev γ) (Lev γ) (Lev (sc γ)) (hd.nm_mem 2) h h h
    (lev_mem hd.su.ord hs)
    (Or.inr (Or.inr (Or.inl ⟨isNum_nm 2, γ, hd.su.inD hγ, sc γ, hd.su.inD hs,
      succR_iff_sc.mpr rfl, (hd.su.levAt hγ).mpr rfl, (hd.su.levAt hs).mpr rfl⟩)))

theorem mem_S {γ : V} (hγ : Ord γ) (h : Lev γ ∈ N) : γ ∈ δ' :=
  (rkL_mem (rkL_lev hγ) hd.su.ord).mp (hd.sub _ h)

theorem op_mem {γ s a b c x : V} (hγ : γ ∈ δ') (hL : Lev γ ∈ N) (hs : s ∈ N) (ha : a ∈ N)
    (hb : b ∈ N) (hc : c ∈ N) (hs' : s ∈ Lev γ) (ha' : a ∈ Lev γ) (hb' : b ∈ Lev γ)
    (hc' : c ∈ Lev γ) (hD : IsD (Lev γ) (LtS γ) s a b c x) : x ∈ N :=
  hd.clo (nm 3) (Lev γ) (kp s a) (kp b c) x (hd.nm_mem 3) hL (hd.kp_mem hs ha) (hd.kp_mem hb hc)
    (def_mem_lev hd.su.ord hγ hs' ha' hb' hc' hD)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨isNum_nm 3, γ, hd.su.inD hγ, opAt_iff.mpr ⟨Lev γ, LtS γ,
      hier_lev hd.su.ord hd.su.hier (hd.su.inD hγ), rfl, s, hs', a, ha', b, hb', c, hc',
      isOp_kp s a, isOp_kp b c, hD⟩⟩))))

theorem closed : Closed (fun a ↦ a ∈ N) :=
  ⟨hd.nm_mem, fun _ hγ h => hd.succ_mem (hd.mem_S hγ h) h,
    fun _ _ _ _ _ _ hγ hL hs h1 h2 h3 hsN h1N h2N h3N hD =>
      hd.op_mem (hd.mem_S hγ hL) hL hsN h1N h2N h3N hs h1 h2 h3 hD⟩

theorem good {a : V} (ha : a ∈ N) : Good (fun a ↦ a ∈ N) a := by
  obtain ⟨β, hβ, hr⟩ := rkL_exists hd.su.ord (hd.sub a ha)
  obtain ⟨-, hLβ⟩ := hd.rk_mem ha hr
  have hLs := hd.succ_mem hβ hLβ
  have haβ : a ∈ Lev (sc β) := inDef_mem hr.1 hr.2.1
  refine ⟨ha, ?_⟩
  rcases ord_tri (ord_sc hr.1) hd.su.big.1 with h | h | h
  · exact ⟨ν, hd.su.big, hd.gen2, lev_mono hd.su.big.1 h a haβ⟩
  · exact ⟨ν, hd.su.big, hd.gen2, h ▸ haβ⟩
  · exact ⟨sc β, ⟨ord_sc hr.1, fun n hn => (ord_sc hr.1).1 ν h n (hd.su.big.2 n hn)⟩, hLs, haβ⟩

theorem ld_mem {a β s y₁ y₂ y₃ : V} (ha : a ∈ N) (hr : RkL β a) (hs : s ∈ Lev β)
    (h1 : y₁ ∈ Lev β) (h2 : y₂ ∈ Lev β) (h3 : y₃ ∈ Lev β)
    (hL : LeastD (Lev β) (LtS β) s y₁ y₂ y₃ a) : s ∈ N ∧ y₁ ∈ N ∧ y₂ ∈ N ∧ y₃ ∈ N := by
  obtain ⟨hβ, -⟩ := hd.rk_mem ha hr
  have hW : ∀ z, z ∈ Lev β → z ∈ Lev δ' := lev_mono hd.su.ord hβ
  have hld : LdAt F β a s y₁ y₂ y₃ := ldAt_iff.mpr ⟨Lev β, LtS β,
    hier_lev hd.su.ord hd.su.hier (hd.su.inD hβ), hs, h1, h2, h3, hL⟩
  have hrk := (hd.su.rkAt hβ).mpr hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hd.clo (nm 4) a a a s (hd.nm_mem 4) ha ha ha (hW s hs)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨isNum_nm 4, β, hd.su.inD hβ, hrk, y₁, hW _ h1,
        y₂, hW _ h2, y₃, hW _ h3, hld⟩)))))
  · exact hd.clo (nm 5) a a a y₁ (hd.nm_mem 5) ha ha ha (hW _ h1)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨isNum_nm 5, β, hd.su.inD hβ, hrk, s,
        hW _ hs, y₂, hW _ h2, y₃, hW _ h3, hld⟩))))))
  · exact hd.clo (nm 6) a a a y₂ (hd.nm_mem 6) ha ha ha (hW _ h2)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨isNum_nm 6, β, hd.su.inD hβ, hrk,
        s, hW _ hs, y₁, hW _ h1, y₃, hW _ h3, hld⟩)))))))
  · exact hd.clo (nm 7) a a a y₃ (hd.nm_mem 7) ha ha ha (hW _ h3)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨isNum_nm 7, β,
        hd.su.inD hβ, hrk, s, hW _ hs, y₁, hW _ h1, y₂, hW _ h2, hld⟩))))))))

/-- **The least member of a set with a member, in the hull, is in the hull.** -/
theorem min_mem {a : V} (ha : a ∈ N) (hne : ∃ z, z ∈ a) :
    ∃ m, m ∈ N ∧ m ∈ a ∧ ∀ z, z ∈ a → ¬LtL z m := by
  have hsub : ∀ z, z ∈ a → z ∈ Lev δ' := fun z hz => lev_tr hd.su.ord a (hd.sub a ha) z hz
  obtain ⟨m, hm, hmin⟩ := ltL_least hd.su.ord a hsub hne
  refine ⟨m, hd.clo (nm 8) a a a m (hd.nm_mem 8) ha ha ha (hsub m hm) ?_, hm, hmin⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨isNum_nm 8, hm,
    fun z hz hp => hmin z hz ((lts_iff hd.su.ord).mp hp).2.2⟩)))))))

/-- The components of a pair in the hull are in the hull. -/
theorem fst_snd_mem {a b : V} (h : kp a b ∈ N) : a ∈ N ∧ b ∈ N := by
  obtain ⟨-, γ, hγ, hLγ, hpγ⟩ := hd.good h
  have hLgood : Good (fun a ↦ a ∈ N) (Lev γ) := hd.good hLγ
  have htr : ∀ y, y ∈ Lev γ → ∀ z, z ∈ y → z ∈ Lev γ := lev_tr hγ.1
  have hp : ∀ i : Fin 1, (![kp a b] : Fin 1 → V) i ∈ Lev γ ∧
      Good (fun a ↦ a ∈ N) ((![kp a b] : Fin 1 → V) i) := fun i => by
    have : i = 0 := Subsingleton.elim _ _
    subst this
    exact ⟨hpγ, hd.good h⟩
  obtain ⟨Y, hY, hYm⟩ := sep_good_bdef hd.closed (k := 1)
    (BDef.bex 1 (BDef.bex 0 (isOpB.comp ![3, 2, 0]))) hLgood htr ![kp a b] hp
  obtain ⟨Y', hY', hYm'⟩ := sep_good_bdef hd.closed (k := 1)
    (BDef.bex 1 (BDef.bex 0 (isOpB.comp ![3, 0, 2]))) hLgood htr ![kp a b] hp
  have hYa : ∀ z, z ∈ Y ↔ z ∈ Lev γ ∧ ∃ u, u ∈ kp a b ∧ ∃ y, y ∈ u ∧ IsOp (kp a b) z y := hYm
  have hYb : ∀ z, z ∈ Y' ↔ z ∈ Lev γ ∧ ∃ u, u ∈ kp a b ∧ ∃ y, y ∈ u ∧ IsOp (kp a b) y z := hYm'
  obtain ⟨u₁, hu₁, hau⟩ := pr_fst_mem (isOp_kp a b)
  obtain ⟨u₂, hu₂, hbu⟩ := pr_snd_mem (isOp_kp a b)
  have haL : a ∈ Lev γ := htr _ (htr _ hpγ u₁ hu₁) a hau
  have hbL : b ∈ Lev γ := htr _ (htr _ hpγ u₂ hu₂) b hbu
  have haY : a ∈ Y := (hYa a).mpr ⟨haL, u₂, hu₂, b, hbu, isOp_kp a b⟩
  have hbY : b ∈ Y' := (hYb b).mpr ⟨hbL, u₁, hu₁, a, hau, isOp_kp a b⟩
  obtain ⟨m, hmN, hmY, -⟩ := hd.min_mem hY.1 ⟨a, haY⟩
  obtain ⟨m', hm'N, hm'Y, -⟩ := hd.min_mem hY'.1 ⟨b, hbY⟩
  obtain ⟨-, u, -, y, -, hop⟩ := (hYa m).mp hmY
  obtain ⟨-, u', -, y', -, hop'⟩ := (hYb m').mp hm'Y
  have e1 := (op_inj hop (isOp_kp a b)).1
  have e2 := (op_inj hop' (isOp_kp a b)).2
  exact ⟨e1 ▸ hmN, e2 ▸ hm'N⟩

end HullData

end setup

/-! ### The collapse of the hull -/

/-- A bounded formula, as a bounded definition of the relation that it defines. -/
def BDef.ofForm {k : ℕ} (φ : Semisentence ℒₛₑₜ k) (h : (Bounding.mem ℒₛₑₜ).Closure φ) :
    BDef (fun V _ v ↦ V ⊧/v φ) where
  φ := φ
  eval _ _ _ := Iff.rfl
  bdd := h

section collapse

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The value at `a` of the function `P`, a set of pairs. -/
noncomputable def piF (P a : V) : V := Classical.epsilon (fun v ↦ Pr P a v)

theorem piF_eq {N T P r a y : V} (h : IsColl P r N T) (ha : a ∈ N) :
    Pr P a y ↔ y = piF P a := by
  obtain ⟨v, -, hpr, huniq, -⟩ := h a ha
  have hs : Pr P a (piF P a) := Classical.epsilon_spec (p := fun v ↦ Pr P a v) ⟨v, hpr⟩
  constructor
  · intro hy
    rw [huniq y hy, huniq _ hs]
  · intro hy
    rw [hy]
    exact hs

theorem piF_mem {N T P r b : V} (h : IsColl P r N T) (hb : b ∈ N) :
    piF P b ∈ T ∧ ∀ y, (y ∈ piF P b ↔ ∃ a, a ∈ N ∧ Pr r a b ∧ y = piF P a) := by
  obtain ⟨v, hvT, hpr, -, hmem⟩ := h b hb
  have e : v = piF P b := (piF_eq h hb).mp hpr
  rw [← e]
  exact ⟨hvT, fun y => (hmem y).trans
    ⟨fun ⟨a, ha, hr, hPa⟩ => ⟨a, ha, hr, (piF_eq h ha).mp hPa⟩,
      fun ⟨a, ha, hr, hy⟩ => ⟨a, ha, hr, (piF_eq h ha).mpr hy⟩⟩⟩

/-- The membership relation on `N`, as a set of pairs. -/
noncomputable def memR (N : V) : V := relB (k := 0) (BDef.mem 0 1) N N ![]

theorem pr_memR {N a b : V} : Pr (memR N) a b ↔ a ∈ N ∧ b ∈ N ∧ a ∈ b := pr_relB _ _ _ _ a b

theorem wf_memR (N : V) : WFon (memR N) N := by
  rintro X ⟨c, hc, -⟩ -
  obtain ⟨m, hm, hmin⟩ := m_found X ⟨c, hc⟩
  exact ⟨m, hm, fun b hb hp => hmin b hb (pr_memR.mp hp).2.2⟩

theorem pi_mem {N T P a : V} (hP : IsColl P (memR N) N T) (ha : a ∈ N) (y : V) :
    y ∈ piF P a ↔ ∃ b, b ∈ N ∧ b ∈ a ∧ y = piF P b :=
  ((piF_mem hP ha).2 y).trans ⟨fun ⟨b, hb, hr, e⟩ => ⟨b, hb, (pr_memR.mp hr).2.2, e⟩,
    fun ⟨b, hb, hba, e⟩ => ⟨b, hb, pr_memR.mpr ⟨hb, ha, hba⟩, e⟩⟩

variable {ν δ' F x₀ N T P : V}

/-- Two different members of the hull are separated by a member of the hull. -/
theorem HullData.ext_wit (hd : HullData ν δ' F x₀ N) {a b : V} (ha : a ∈ N) (hb : b ∈ N)
    (hne : a ≠ b) : ∃ c, c ∈ N ∧ ((c ∈ a ∧ ¬c ∈ b) ∨ (c ∈ b ∧ ¬c ∈ a)) := by
  have h1 : Good (fun a ↦ a ∈ N) (diffS a b) :=
    good_diff hd.closed (hd.good ha) (hd.good hb) (fun z => mem_diffS)
  have h2 : Good (fun a ↦ a ∈ N) (diffS b a) :=
    good_diff hd.closed (hd.good hb) (hd.good ha) (fun z => mem_diffS)
  by_cases hne1 : ∃ z, z ∈ diffS a b
  · obtain ⟨m, hmN, hm, -⟩ := hd.min_mem h1.1 hne1
    exact ⟨m, hmN, Or.inl (mem_diffS.mp hm)⟩
  · by_cases hne2 : ∃ z, z ∈ diffS b a
    · obtain ⟨m, hmN, hm, -⟩ := hd.min_mem h2.1 hne2
      exact ⟨m, hmN, Or.inr (mem_diffS.mp hm)⟩
    · exfalso
      apply hne
      exact mem_ext fun z =>
        ⟨fun hz => by
          by_contra hn
          exact hne1 ⟨z, mem_diffS.mpr ⟨hz, hn⟩⟩,
        fun hz => by
          by_contra hn
          exact hne2 ⟨z, mem_diffS.mpr ⟨hz, hn⟩⟩⟩

/-- **The collapse is one-to-one on the hull.** -/
theorem pi_inj (hd : HullData ν δ' F x₀ N) (hP : IsColl P (memR N) N T) :
    ∀ a, a ∈ N → ∀ b, b ∈ N → piF P a = piF P b → a = b := by
  by_contra hcon
  let Z : V := sepB (k := 3) (BDef.bex 1 (BDef.bex 3 ((prB.comp ![5, 2, 0]).and
    ((prB.comp ![5, 1, 0]).and (BDef.eq 2 1).not)))) N ![N, T, P]
  have hZ : ∀ a, a ∈ Z ↔ a ∈ N ∧ ∃ b, b ∈ N ∧ ∃ v, v ∈ T ∧ (Pr P a v ∧ (Pr P b v ∧ ¬a = b)) :=
    fun a => mem_sepB _ _ _ a
  have hZ' : ∀ a, a ∈ Z ↔ a ∈ N ∧ ∃ b, b ∈ N ∧ piF P a = piF P b ∧ a ≠ b := by
    intro a
    rw [hZ]
    constructor
    · rintro ⟨ha, b, hb, v, -, h1, h2, hne⟩
      exact ⟨ha, b, hb, ((piF_eq hP ha).mp h1).symm.trans ((piF_eq hP hb).mp h2), hne⟩
    · rintro ⟨ha, b, hb, e, hne⟩
      exact ⟨ha, b, hb, piF P a, (piF_mem hP ha).1, (piF_eq hP ha).mpr rfl,
        (piF_eq hP hb).mpr e, hne⟩
  have hne : ∃ a, a ∈ Z := by
    by_contra h
    refine hcon fun a ha b hb e => ?_
    by_contra hn
    exact h ⟨a, (hZ' a).mpr ⟨ha, b, hb, e, hn⟩⟩
  obtain ⟨a, haZ, hmin⟩ := m_found Z hne
  obtain ⟨ha, b, hb, e, hn⟩ := (hZ' a).mp haZ
  obtain ⟨c, hc, h | h⟩ := hd.ext_wit ha hb hn
  · have h1 : piF P c ∈ piF P b := by
      rw [← e]
      exact (pi_mem hP ha _).mpr ⟨c, hc, h.1, rfl⟩
    obtain ⟨c', hc', hc'b, e'⟩ := (pi_mem hP hb _).mp h1
    have hne' : c ≠ c' := fun e'' => h.2 (e'' ▸ hc'b)
    exact hmin c ((hZ' c).mpr ⟨hc, c', hc', e', hne'⟩) h.1
  · have h1 : piF P c ∈ piF P a := by
      rw [e]
      exact (pi_mem hP hb _).mpr ⟨c, hc, h.1, rfl⟩
    obtain ⟨c', hc', hc'a, e'⟩ := (pi_mem hP ha _).mp h1
    have hne' : c' ≠ c := fun e'' => h.2 (e'' ▸ hc'a)
    exact hmin c' ((hZ' c').mpr ⟨hc', c, hc, e'.symm, hne'⟩) hc'a

theorem pi_mem_iff (hd : HullData ν δ' F x₀ N) (hP : IsColl P (memR N) N T) {a b : V}
    (ha : a ∈ N) (hb : b ∈ N) : a ∈ b ↔ piF P a ∈ piF P b := by
  constructor
  · intro h
    exact (pi_mem hP hb _).mpr ⟨a, ha, h, rfl⟩
  · intro h
    obtain ⟨c, hc, hcb, e⟩ := (pi_mem hP hb _).mp h
    rw [pi_inj hd hP a ha c hc e]
    exact hcb

/-- The collapse is the identity on a transitive part of the hull. -/
theorem pi_id (hP : IsColl P (memR N) N T) {t : V} (ht : ∀ a, a ∈ t → a ∈ N)
    (htr : ∀ a, a ∈ t → ∀ z, z ∈ a → z ∈ t) : ∀ a, a ∈ t → piF P a = a := by
  by_contra hcon
  let Z : V := sepB (k := 2) (BDef.bex 1 ((prB.comp ![3, 1, 0]).and (BDef.eq 0 1).not)) t
    ![T, P]
  have hZ : ∀ a, a ∈ Z ↔ a ∈ t ∧ ∃ v, v ∈ T ∧ (Pr P a v ∧ ¬v = a) := fun a => mem_sepB _ _ _ a
  have hZ' : ∀ a, a ∈ Z ↔ a ∈ t ∧ piF P a ≠ a := by
    intro a
    rw [hZ]
    constructor
    · rintro ⟨ha, v, -, h1, hne⟩
      exact ⟨ha, (piF_eq hP (ht a ha)).mp h1 ▸ hne⟩
    · rintro ⟨ha, hne⟩
      exact ⟨ha, piF P a, (piF_mem hP (ht a ha)).1, (piF_eq hP (ht a ha)).mpr rfl, hne⟩
  have hne : ∃ a, a ∈ Z := by
    by_contra h
    refine hcon fun a ha => ?_
    by_contra hn
    exact h ⟨a, (hZ' a).mpr ⟨ha, hn⟩⟩
  obtain ⟨a, haZ, hmin⟩ := m_found Z hne
  obtain ⟨ha, hn⟩ := (hZ' a).mp haZ
  have hlow : ∀ b, b ∈ a → piF P b = b := by
    intro b hb
    by_contra hnb
    exact hmin b ((hZ' b).mpr ⟨htr a ha b hb, hnb⟩) hb
  apply hn
  refine mem_ext fun y => ?_
  rw [pi_mem hP (ht a ha)]
  constructor
  · rintro ⟨b, -, hb, e⟩
    rw [e, hlow b hb]
    exact hb
  · intro hy
    exact ⟨y, ht y (htr a ha y hy), hy, (hlow y hy).symm⟩

/-- A level in the hull that contains finitely many members of the hull. -/
theorem HullData.level_fin (hd : HullData ν δ' F x₀ N) : ∀ {n : ℕ} (e : Fin n → V),
    (∀ i, e i ∈ N) → ∃ γ, Big γ ∧ Lev γ ∈ N ∧ ∀ i, e i ∈ Lev γ
  | 0, _, _ => ⟨ν, hd.su.big, hd.gen2, fun i => i.elim0⟩
  | n + 1, e, he => by
    obtain ⟨γ₁, g₁, L₁, h₁⟩ := hd.level_fin (fun i ↦ e i.succ) (fun i => he i.succ)
    obtain ⟨-, γ₂, g₂, L₂, h₂⟩ := hd.good (he 0)
    rcases ord_tri g₁.1 g₂.1 with h | h | h
    · refine ⟨γ₂, g₂, L₂, fun i => ?_⟩
      cases i using Fin.cases with
      | zero => exact h₂
      | succ i => exact lev_mono g₂.1 h _ (h₁ i)
    · refine ⟨γ₂, g₂, L₂, fun i => ?_⟩
      cases i using Fin.cases with
      | zero => exact h₂
      | succ i => exact h ▸ h₁ i
    · refine ⟨γ₁, g₁, L₁, fun i => ?_⟩
      cases i using Fin.cases with
      | zero => exact lev_mono g₁.1 h _ h₂
      | succ i => exact h₁ i

lemma val_pos {n : ℕ} (t : Semiterm ℒₛₑₜ Empty (n + 1)) (ht : t.Positive) :
    ∃ j : Fin n, ∀ (x : V) (e : Fin n → V), t.val (M := V) (x :> e) Empty.elim = e j := by
  match t with
  | #i =>
    cases i using Fin.cases with
    | zero => simp [Semiterm.Positive] at ht
    | succ j => exact ⟨j, by simp⟩
  | &k => exact k.elim
  | .func f _ => exact Empty.elim f

/-- **The collapse of the hull preserves the bounded formulas.** -/
theorem elem_form (hd : HullData ν δ' F x₀ N) (hP : IsColl P (memR N) N T) :
    ∀ {n : ℕ} {φ : Semiformula ℒₛₑₜ Empty n}, (Bounding.mem ℒₛₑₜ).Closure φ →
      ∀ e : Fin n → V, (∀ i, e i ∈ N) →
        (Eval (M := V) e Empty.elim φ ↔ Eval (M := V) (fun i ↦ piF P (e i)) Empty.elim φ) := by
  intro n φ h
  induction h with
  | verum n => intro e _; simp
  | falsum n => intro e _; simp
  | rel r v =>
    intro e he
    cases r with
    | eq =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      show (Semiterm.val (M := V) e Empty.elim (v 0) = Semiterm.val (M := V) e Empty.elim (v 1)) ↔
        (Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 0) =
          Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 1))
      rw [hi, hj]
      simp only [Semiterm.val_bvar]
      exact ⟨fun h => by rw [h], fun h => pi_inj hd hP _ (he i) _ (he j) h⟩
    | mem =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      show (Semiterm.val (M := V) e Empty.elim (v 0) ∈ Semiterm.val (M := V) e Empty.elim (v 1)) ↔
        (Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 0) ∈
          Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 1))
      rw [hi, hj]
      simp only [Semiterm.val_bvar]
      exact pi_mem_iff hd hP (he i) (he j)
  | nrel r v =>
    intro e he
    cases r with
    | eq =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      show ¬(Semiterm.val (M := V) e Empty.elim (v 0) = Semiterm.val (M := V) e Empty.elim (v 1)) ↔
        ¬(Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 0) =
          Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 1))
      rw [hi, hj]
      simp only [Semiterm.val_bvar]
      exact not_congr ⟨fun h => by rw [h], fun h => pi_inj hd hP _ (he i) _ (he j) h⟩
    | mem =>
      obtain ⟨i, hi⟩ := term_cases (v 0)
      obtain ⟨j, hj⟩ := term_cases (v 1)
      show ¬(Semiterm.val (M := V) e Empty.elim (v 0) ∈ Semiterm.val (M := V) e Empty.elim (v 1)) ↔
        ¬(Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 0) ∈
          Semiterm.val (M := V) (fun i ↦ piF P (e i)) Empty.elim (v 1))
      rw [hi, hj]
      simp only [Semiterm.val_bvar]
      exact not_congr (pi_mem_iff hd hP (he i) (he j))
  | and _ _ ih₁ ih₂ => intro e he; simp [ih₁ e he, ih₂ e he]
  | or _ _ ih₁ ih₂ => intro e he; simp [ih₁ e he, ih₂ e he]
  | @ball n R φ t hR ht hφ ih =>
    intro e he
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨j, hj⟩ := val_pos (V := V) t ht
    have key : ∀ x : V, (fun i ↦ piF P ((x :> e) i)) = (piF P x :> fun i ↦ piF P (e i)) := by
      intro x; funext i; cases i using Fin.cases <;> simp
    have hcons : ∀ x : V, x ∈ N → ∀ i, (x :> e) i ∈ N := by
      intro x hx i
      cases i using Fin.cases with
      | zero => exact hx
      | succ i => exact he i
    simp only [eval_ball, eval_memOp, Matrix.cons_val_zero, hj]
    constructor
    · intro H xb hxb
      obtain ⟨x, hxN, hx, rfl⟩ := (pi_mem hP (he j) xb).mp hxb
      have := (ih (x :> e) (hcons x hxN)).mp (H x hx)
      rwa [key] at this
    · intro H x hx
      by_contra hn
      obtain ⟨γ, hγ, hL, hl⟩ := hd.level_fin e he
      obtain ⟨Y, hY, hYm⟩ := sep_good_bdef hd.closed (k := n)
        ((BDef.mem 0 j.succ).and (BDef.ofForm φ hφ).not) (hd.good hL) (lev_tr hγ.1) e
        (fun i => ⟨hl i, hd.good (he i)⟩)
      have hYm' : ∀ z, z ∈ Y ↔ z ∈ Lev γ ∧ (z ∈ e j ∧ ¬Eval (M := V) (z :> e) Empty.elim φ) :=
        fun z => hYm z
      obtain ⟨m, hmN, hmY, -⟩ := hd.min_mem hY.1
        ⟨x, (hYm' x).mpr ⟨lev_tr hγ.1 _ (hl j) x hx, hx, hn⟩⟩
      obtain ⟨-, hmj, hmn⟩ := (hYm' m).mp hmY
      apply hmn
      refine (ih (m :> e) (hcons m hmN)).mpr ?_
      rw [key]
      exact H (piF P m) ((pi_mem hP (he j) _).mpr ⟨m, hmN, hmj, rfl⟩)
  | @bexs n R φ t hR ht hφ ih =>
    intro e he
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨j, hj⟩ := val_pos (V := V) t ht
    have key : ∀ x : V, (fun i ↦ piF P ((x :> e) i)) = (piF P x :> fun i ↦ piF P (e i)) := by
      intro x; funext i; cases i using Fin.cases <;> simp
    have hcons : ∀ x : V, x ∈ N → ∀ i, (x :> e) i ∈ N := by
      intro x hx i
      cases i using Fin.cases with
      | zero => exact hx
      | succ i => exact he i
    simp only [eval_bexs, eval_memOp, Matrix.cons_val_zero, hj]
    constructor
    · rintro ⟨x, hx, hφx⟩
      obtain ⟨γ, hγ, hL, hl⟩ := hd.level_fin e he
      obtain ⟨Y, hY, hYm⟩ := sep_good_bdef hd.closed (k := n)
        ((BDef.mem 0 j.succ).and (BDef.ofForm φ hφ)) (hd.good hL) (lev_tr hγ.1) e
        (fun i => ⟨hl i, hd.good (he i)⟩)
      have hYm' : ∀ z, z ∈ Y ↔ z ∈ Lev γ ∧ (z ∈ e j ∧ Eval (M := V) (z :> e) Empty.elim φ) :=
        fun z => hYm z
      obtain ⟨m, hmN, hmY, -⟩ := hd.min_mem hY.1
        ⟨x, (hYm' x).mpr ⟨lev_tr hγ.1 _ (hl j) x hx, hx, hφx⟩⟩
      obtain ⟨-, hmj, hmφ⟩ := (hYm' m).mp hmY
      refine ⟨piF P m, (pi_mem hP (he j) _).mpr ⟨m, hmN, hmj, rfl⟩, ?_⟩
      have := (ih (m :> e) (hcons m hmN)).mp hmφ
      rwa [key] at this
    · rintro ⟨xb, hxb, hφxb⟩
      obtain ⟨x, hxN, hx, rfl⟩ := (pi_mem hP (he j) xb).mp hxb
      refine ⟨x, hx, (ih (x :> e) (hcons x hxN)).mpr ?_⟩
      rw [key]
      exact hφxb

/-- **The collapse of the hull preserves the relations with a bounded definition.** -/
theorem elem_bdef (hd : HullData ν δ' F x₀ N) (hP : IsColl P (memR N) N T) {k : ℕ}
    {R : MRel k} (d : BDef R) (v : Fin k → V) (hv : ∀ i, v i ∈ N) :
    R V v ↔ R V (fun i ↦ piF P (v i)) :=
  (d.eval V v).symm.trans ((elem_form hd hP d.bdd v hv).trans (d.eval V _))

end collapse

/-! ### The collapsed hull is a level -/

section defs2

variable {V : Type} [SetStructure V]

/-- The bounded form of the statement of the induction, for a level `A` and the level `Ab` at
the collapsed ordinal: the collapse `P` maps the members of the hull in `A` onto `Ab`, and it
preserves the order. -/
def GoodAt (A Ab N P lt' lb T : V) : Prop :=
  (∀ z, z ∈ Ab → ∃ b, b ∈ A ∧ (b ∈ N ∧ Pr P b z)) ∧
  ((∀ b, b ∈ A → b ∈ N → ∃ z, z ∈ Ab ∧ Pr P b z) ∧
  (∀ a, a ∈ A → ∀ b, b ∈ A → a ∈ N → b ∈ N → ∀ ab, ab ∈ T → ∀ bb, bb ∈ T →
    Pr P a ab → Pr P b bb → (Pr lt' a b ↔ Pr lb ab bb)))

end defs2

def goodAtB : BDef (k := 7) (fun V _ v ↦ GoodAt (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  ((BDef.ball 1 (BDef.bex 1 ((BDef.mem 0 4).and (prB.comp ![5, 0, 1])))).and
  ((BDef.ball 0 ((BDef.mem 0 3).imp (BDef.bex 2 (prB.comp ![5, 1, 0])))).and
  (BDef.ball 0 (BDef.ball 1 ((BDef.mem 1 4).imp ((BDef.mem 0 4).imp (BDef.ball 8 (BDef.ball 9
    ((prB.comp ![7, 3, 1]).imp ((prB.comp ![7, 2, 0]).imp
      ((prB.comp ![8, 3, 2]).iff (prB.comp ![9, 1, 0])))))))))))).congr fun _ _ _ => Iff.rfl

/-- The ordinals at which the bounded form of the statement fails. -/
def badB : BDef (k := 10) (fun V _ v ↦ ∃ A, A ∈ v 1 ∧ (LevAt (v 2) (v 0) A ∧
    ∃ αb, αb ∈ v 3 ∧ (Pr (v 4) A αb ∧ ∃ Ab, Ab ∈ v 5 ∧ (LevAt (v 6) αb Ab ∧
      ¬GoodAt A Ab (v 1) (v 7) (v 8) (v 9) (v 3))))) :=
  (BDef.bex 1 ((levAtB.comp ![3, 1, 0]).and (BDef.bex 4 ((prB.comp ![6, 1, 0]).and
    (BDef.bex 7 ((levAtB.comp ![9, 1, 0]).and
      (goodAtB.comp ![2, 0, 4, 10, 11, 12, 6]).not)))))).congr fun _ _ _ => Iff.rfl

section cond

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem fin4_all {α : Type} {p : α → Prop} {a b c d : α} (ha : p a) (hb : p b) (hc : p c)
    (hd : p d) : ∀ i : Fin 4, p ((![a, b, c, d] : Fin 4 → α) i) := by
  intro i
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | 2 => exact hc
  | 3 => exact hd

theorem lts_pair {γ q : V} (hγ : Ord γ) (hq : q ∈ LtS γ) :
    ∃ a b, q = kp a b ∧ Pr (LtS γ) a b := by
  obtain ⟨F, hF⟩ := exists_hier hγ
  obtain ⟨A, lt, hpr, -, -, hc, -⟩ := hier_at hF (self_mem_sc γ)
  obtain ⟨rfl, rfl⟩ := hier_lev_eq hγ hF (self_mem_sc γ) hpr
  obtain ⟨a, -, b, -, hop⟩ := hc q hq
  exact ⟨a, b, isOp_iff.mp hop, ⟨q, hq, hop⟩⟩

theorem ltL_iff_rk {β₁ β₂ x x' : V} (r₁ : RkL β₁ x) (r₂ : RkL β₂ x') :
    LtL x x' ↔ (β₁ ∈ β₂ ∨ (β₁ = β₂ ∧ SameLess (Lev β₁) (LtS β₁) x x')) := by
  constructor
  · rintro ⟨b₁, b₂, s₁, s₂, h⟩
    have e1 := rkL_unique s₁ r₁
    have e2 := rkL_unique s₂ r₂
    rw [e1, e2] at h
    exact h
  · intro h
    exact ⟨β₁, β₂, r₁, r₂, h⟩

theorem exists_lim2 {a b : V} (ha : Ord a) (hb : Ord b) :
    ∃ lam : V, Lim lam ∧ a ∈ lam ∧ b ∈ lam := by
  rcases ord_tri ha hb with h | h | h
  · obtain ⟨lam, hl, hbl⟩ := exists_lim hb
    exact ⟨lam, hl, hl.1.1 b hbl a h, hbl⟩
  · obtain ⟨lam, hl, hbl⟩ := exists_lim hb
    exact ⟨lam, hl, by rw [h]; exact hbl, hbl⟩
  · obtain ⟨lam, hl, hal⟩ := exists_lim ha
    exact ⟨lam, hl, hal, hl.1.1 a hal b h⟩

/-- The relation between two levels in `N`, the first at a smaller ordinal. -/
noncomputable def levR (N F D : V) : V :=
  relB (k := 2) (BDef.bex 3 (BDef.bex 0 ((levAtB.comp ![4, 0, 2]).and
    (levAtB.comp ![4, 1, 3])))) N N ![F, D]

theorem pr_levR {N F D a b : V} : Pr (levR N F D) a b ↔ a ∈ N ∧ b ∈ N ∧
    ∃ γ, γ ∈ D ∧ ∃ γ', γ' ∈ γ ∧ (LevAt F γ' a ∧ LevAt F γ b) := pr_relB _ _ _ _ a b

theorem wf_levR {ν δ' F x₀ N : V} (hd : HullData ν δ' F x₀ N) :
    WFon (levR N F (sc δ')) N := by
  have su := hd.su
  rintro X ⟨c, hc, -⟩ -
  obtain ⟨m, hm, hmin⟩ := m_found X ⟨c, hc⟩
  refine ⟨m, hm, fun b hb hp => ?_⟩
  obtain ⟨-, -, γ, hγ, γ', hγ', h1, h2⟩ := pr_levR.mp hp
  have e1 := (levAt_lev su.ord su.hier ((ord_sc su.ord).1 γ hγ γ' hγ')).mp h1
  have e2 := (levAt_lev su.ord su.hier hγ).mp h2
  apply hmin b hb
  rw [e1, e2]
  exact lev_mem (ord_mem (ord_sc su.ord) hγ) hγ'

/-- The ordinals in `T`. -/
noncomputable def kap (T : V) : V := sepB (k := 0) (ordB.comp ![0]) T ![]

theorem mem_kap {T α : V} : α ∈ kap T ↔ α ∈ T ∧ Ord α := mem_sepB _ _ _ α

theorem ord_kap {T : V} (hT : Tr T) : Ord (kap T) :=
  ⟨fun y hy z hz => mem_kap.mpr ⟨hT y (mem_kap.mp hy).1 z hz, ord_mem (mem_kap.mp hy).2 hz⟩,
    fun y hy => (mem_kap.mp hy).2.1⟩

/-- The collapse of the ordinals whose level is in the hull. -/
noncomputable def ccF (Q γ : V) : V := piF Q (Lev γ)

/-- `γ` is an ordinal below `δ'` whose level is in the hull. -/
def InS (N δ' γ : V) : Prop := γ ∈ δ' ∧ Lev γ ∈ N

/-- The collapse `P` maps the members of the hull in the level at `γ` onto the level at the
collapsed ordinal. -/
def StA (N P Q γ : V) : Prop :=
  ∀ z, z ∈ Lev (ccF Q γ) ↔ ∃ b, b ∈ N ∧ b ∈ Lev γ ∧ z = piF P b

/-- The collapse `P` preserves the order of the members of the hull in the level at `γ`. -/
def StC (N P γ : V) : Prop :=
  ∀ a b, a ∈ N → b ∈ N → a ∈ Lev γ → b ∈ Lev γ → (LtL a b ↔ LtL (piF P a) (piF P b))

/-- The hull with its two collapses: `P` of the hull, and `Q` of the levels in the hull. -/
structure CollData (ν δ' F x₀ N T P Q : V) : Prop where
  hd : HullData ν δ' F x₀ N
  trT : Tr T
  hP : IsColl P (memR N) N T
  hQ : IsColl Q (levR N F (sc δ')) N T

namespace CollData

variable {ν δ' F x₀ N T P Q : V} (cd : CollData ν δ' F x₀ N T P Q)

include cd

theorem pr_lev {a b : V} : Pr (levR N F (sc δ')) a b ↔ a ∈ N ∧ b ∈ N ∧
    ∃ γ, γ ∈ δ' ∧ ∃ γ', γ' ∈ γ ∧ (a = Lev γ' ∧ b = Lev γ) := by
  rw [pr_levR]
  have su := cd.hd.su
  constructor
  · rintro ⟨ha, hb, γ, hγ, γ', hγ', h1, h2⟩
    have hγO := ord_mem (ord_sc su.ord) hγ
    have e2 := (levAt_lev su.ord su.hier hγ).mp h2
    have hγδ : γ ∈ δ' := cd.hd.mem_S hγO (e2 ▸ hb)
    have e1 := (su.levAt (su.ord.1 γ hγδ γ' hγ')).mp h1
    exact ⟨ha, hb, γ, hγδ, γ', hγ', e1, e2⟩
  · rintro ⟨ha, hb, γ, hγ, γ', hγ', e1, e2⟩
    exact ⟨ha, hb, γ, su.inD hγ, γ', hγ', (su.levAt (su.ord.1 γ hγ γ' hγ')).mpr e1,
      (su.levAt hγ).mpr e2⟩

theorem cc_mem {γ : V} (hγ : InS N δ' γ) (y : V) :
    y ∈ ccF Q γ ↔ ∃ β, β ∈ γ ∧ Lev β ∈ N ∧ y = ccF Q β := by
  have su := cd.hd.su
  rw [ccF, (piF_mem cd.hQ hγ.2).2 y]
  constructor
  · rintro ⟨a, -, hr, e⟩
    obtain ⟨ha, -, γ₂, hγ₂, γ', hγ', e1, e2⟩ := cd.pr_lev.mp hr
    have e3 : γ = γ₂ := lev_inj (ord_mem su.ord hγ.1) (ord_mem su.ord hγ₂) e2
    rw [← e3] at hγ'
    rw [e1] at ha e
    exact ⟨γ', hγ', ha, e⟩
  · rintro ⟨β, hβ, hβN, e⟩
    exact ⟨Lev β, hβN, cd.pr_lev.mpr ⟨hβN, hγ.2, γ, hγ.1, β, hβ, rfl, rfl⟩, e⟩

theorem cc_T {γ : V} (hγ : InS N δ' γ) : ccF Q γ ∈ T := (piF_mem cd.hQ hγ.2).1

theorem inS_of_mem {γ β : V} (hγ : InS N δ' γ) (hβ : β ∈ γ) (hβN : Lev β ∈ N) : InS N δ' β :=
  ⟨cd.hd.su.ord.1 γ hγ.1 β hβ, hβN⟩

theorem cc_tr {γ : V} (hγ : InS N δ' γ) : Tr (ccF Q γ) := by
  intro y hy z hz
  obtain ⟨β, hβ, hβN, rfl⟩ := (cd.cc_mem hγ y).mp hy
  obtain ⟨β', hβ', hβ'N, rfl⟩ := (cd.cc_mem (cd.inS_of_mem hγ hβ hβN) z).mp hz
  have hγO := ord_mem cd.hd.su.ord hγ.1
  exact (cd.cc_mem hγ _).mpr ⟨β', hγO.1 β hβ β' hβ', hβ'N, rfl⟩

theorem cc_ord {γ : V} (hγ : InS N δ' γ) : Ord (ccF Q γ) :=
  ⟨cd.cc_tr hγ, fun y hy => by
    obtain ⟨β, hβ, hβN, rfl⟩ := (cd.cc_mem hγ y).mp hy
    exact cd.cc_tr (cd.inS_of_mem hγ hβ hβN)⟩

theorem cc_lt {β γ : V} (hβ : InS N δ' β) (hγ : InS N δ' γ) :
    β ∈ γ ↔ ccF Q β ∈ ccF Q γ := by
  constructor
  · intro h
    exact (cd.cc_mem hγ _).mpr ⟨β, h, hβ.2, rfl⟩
  · intro h
    obtain ⟨β', hβ', hβ'N, e⟩ := (cd.cc_mem hγ _).mp h
    have hβ'S := cd.inS_of_mem hγ hβ' hβ'N
    rcases ord_tri (ord_mem cd.hd.su.ord hβ.1) (ord_mem cd.hd.su.ord hβ'S.1) with h1 | h1 | h1
    · have := (cd.cc_mem hβ'S _).mpr ⟨β, h1, hβ.2, rfl⟩
      rw [← e] at this
      exact absurd this (mem_irrefl _)
    · rw [h1]
      exact hβ'
    · have := (cd.cc_mem hβ _).mpr ⟨β', h1, hβ'N, rfl⟩
      rw [← e] at this
      exact absurd this (mem_irrefl _)

theorem cc_inj {β γ : V} (hβ : InS N δ' β) (hγ : InS N δ' γ) (e : ccF Q β = ccF Q γ) :
    β = γ := by
  rcases ord_tri (ord_mem cd.hd.su.ord hβ.1) (ord_mem cd.hd.su.ord hγ.1) with h | h | h
  · have := (cd.cc_lt hβ hγ).mp h
    rw [e] at this
    exact absurd this (mem_irrefl _)
  · exact h
  · have := (cd.cc_lt hγ hβ).mp h
    rw [e] at this
    exact absurd this (mem_irrefl _)

theorem cc_kap {γ : V} (hγ : InS N δ' γ) : ccF Q γ ∈ kap T :=
  mem_kap.mpr ⟨cd.cc_T hγ, cd.cc_ord hγ⟩

/-- The collapse is the identity on `x₀`. -/
theorem pi_x0 : piF P x₀ = x₀ := by
  have hid := pi_id cd.hP (t := Lev ν) cd.hd.gen1 (lev_tr cd.hd.su.big.1)
  refine mem_ext fun y => ?_
  rw [pi_mem cd.hP cd.hd.gen3]
  constructor
  · rintro ⟨b, -, hb, e⟩
    rw [e, hid b (cd.hd.su.sub b hb)]
    exact hb
  · intro hy
    exact ⟨y, cd.hd.gen1 y (cd.hd.su.sub y hy), hy, (hid y (cd.hd.su.sub y hy)).symm⟩

theorem pi_kp {a b : V} (ha : a ∈ N) (hb : b ∈ N) :
    piF P (kp a b) = kp (piF P a) (piF P b) := by
  have h : IsOp (piF P (kp a b)) (piF P a) (piF P b) :=
    (elem_bdef cd.hd cd.hP isOpB ![kp a b, a, b] (by
      intro i
      match i with
      | 0 => exact cd.hd.kp_mem ha hb
      | 1 => exact ha
      | 2 => exact hb)).mp (isOp_kp a b)
  exact isOp_iff.mp h

variable {ρ : V} (hρ : InS N δ' ρ) (hA : StA N P Q ρ) (hC : StC N P ρ)

include hρ hA in
theorem pi_lev : piF P (Lev ρ) = Lev (ccF Q ρ) :=
  mem_ext fun y => (pi_mem cd.hP hρ.2 y).trans (hA y).symm

omit cd in
include hA in
theorem pi_in {a : V} (ha : a ∈ N) (haL : a ∈ Lev ρ) : piF P a ∈ Lev (ccF Q ρ) :=
  (hA _).mpr ⟨a, ha, haL, rfl⟩

include hρ hA hC in
theorem lts_pi {a b : V} (ha : a ∈ N) (hb : b ∈ N) (haL : a ∈ Lev ρ) (hbL : b ∈ Lev ρ) :
    Pr (LtS ρ) a b ↔ Pr (LtS (ccF Q ρ)) (piF P a) (piF P b) := by
  rw [lts_iff (ord_mem cd.hd.su.ord hρ.1), lts_iff (cd.cc_ord hρ)]
  constructor
  · rintro ⟨-, -, h⟩
    exact ⟨pi_in hA ha haL, pi_in hA hb hbL, (hC a b ha hb haL hbL).mp h⟩
  · rintro ⟨-, -, h⟩
    exact ⟨haL, hbL, (hC a b ha hb haL hbL).mpr h⟩

include hρ hA hC in
theorem mem_lts_pi {z : V} (hz : z ∈ N) : z ∈ LtS ρ ↔ piF P z ∈ LtS (ccF Q ρ) := by
  have hρO := ord_mem cd.hd.su.ord hρ.1
  have hcO := cd.cc_ord hρ
  constructor
  · intro h
    obtain ⟨a, b, e, hpr⟩ := lts_pair hρO h
    rw [e] at hz ⊢
    obtain ⟨ha, hb⟩ := cd.hd.fst_snd_mem hz
    obtain ⟨haL, hbL, -⟩ := (lts_iff hρO).mp hpr
    rw [cd.pi_kp ha hb]
    exact pr_iff.mp ((cd.lts_pi hρ hA hC ha hb haL hbL).mp hpr)
  · intro h
    obtain ⟨ab, bb, e, hpr⟩ := lts_pair hcO h
    obtain ⟨habL, hbbL, -⟩ := (lts_iff hcO).mp hpr
    obtain ⟨a, ha, haL, ea⟩ := (hA ab).mp habL
    obtain ⟨b, hb, hbL, eb⟩ := (hA bb).mp hbbL
    rw [ea, eb] at e hpr
    have e' : z = kp a b := pi_inj cd.hd cd.hP z hz (kp a b) (cd.hd.kp_mem ha hb)
      (e.trans (cd.pi_kp ha hb).symm)
    rw [e']
    exact pr_iff.mp ((cd.lts_pi hρ hA hC ha hb haL hbL).mpr hpr)

include hρ hA hC in
theorem phi_pi {z s y₁ y₂ y₃ : V} (hz : z ∈ N) (hs : s ∈ N) (h1 : y₁ ∈ N) (h2 : y₂ ∈ N)
    (h3 : y₃ ∈ N) : Phi (LtS ρ) z s y₁ y₂ y₃ ↔
      Phi (LtS (ccF Q ρ)) (piF P z) (piF P s) (piF P y₁) (piF P y₂) (piF P y₃) := by
  have e1 : PhiE z s y₁ y₂ y₃ ↔ PhiE (piF P z) (piF P s) (piF P y₁) (piF P y₂) (piF P y₃) :=
    elem_bdef cd.hd cd.hP phiEB ![z, s, y₁, y₂, y₃] (by
      intro i
      match i with
      | 0 => exact hz
      | 1 => exact hs
      | 2 => exact h1
      | 3 => exact h2
      | 4 => exact h3)
  have e2 : IsNum 7 s ↔ IsNum 7 (piF P s) :=
    elem_bdef cd.hd cd.hP (isNumB 7) ![s] (by
      intro i
      match i with
      | 0 => exact hs)
  exact or_congr e1 (and_congr e2 (cd.mem_lts_pi hρ hA hC hz))

include hρ hA hC in
theorem pi_isD {s y₁ y₂ y₃ x : V} (hs : s ∈ N) (h1 : y₁ ∈ N) (h2 : y₂ ∈ N) (h3 : y₃ ∈ N)
    (hx : x ∈ N) (hD : IsD (Lev ρ) (LtS ρ) s y₁ y₂ y₃ x) :
    IsD (Lev (ccF Q ρ)) (LtS (ccF Q ρ)) (piF P s) (piF P y₁) (piF P y₂) (piF P y₃) (piF P x) := by
  refine ⟨fun zb hzb => ?_, fun zb hzb hph => ?_⟩
  · obtain ⟨z, hz, hzx, rfl⟩ := (pi_mem cd.hP hx zb).mp hzb
    obtain ⟨hzL, hph⟩ := hD.1 z hzx
    exact ⟨pi_in hA hz hzL, (cd.phi_pi hρ hA hC hz hs h1 h2 h3).mp hph⟩
  · obtain ⟨z, hz, hzL, rfl⟩ := (hA zb).mp hzb
    exact (pi_mem cd.hP hx _).mpr
      ⟨z, hz, hD.2 z hzL ((cd.phi_pi hρ hA hC hz hs h1 h2 h3).mpr hph), rfl⟩

include hρ hA hC in
theorem pi_inDef {a : V} (ha : a ∈ N) (hr : RkL ρ a) :
    InDef (Lev (ccF Q ρ)) (LtS (ccF Q ρ)) (piF P a) := by
  have hρO := hr.1
  by_cases e : a = Lev ρ
  · left
    rw [e]
    exact cd.pi_lev hρ hA
  · obtain ⟨s, hs, y₁, h1, y₂, h2, y₃, h3, hL⟩ := leastD_exists hρO (wol hρO) hr.2.1 e
    obtain ⟨hsN, h1N, h2N, h3N⟩ := cd.hd.ld_mem ha hr hs h1 h2 h3 hL
    exact Or.inr ⟨_, pi_in hA hsN hs, _, pi_in hA h1N h1, _, pi_in hA h2N h2, _,
      pi_in hA h3N h3, cd.pi_isD hρ hA hC hsN h1N h2N h3N ha hL.1⟩

include hρ hA hC in
theorem pi_rk {a : V} (ha : a ∈ N) (hr : RkL ρ a) : RkL (ccF Q ρ) (piF P a) := by
  have hcO := cd.cc_ord hρ
  refine ⟨hcO, cd.pi_inDef hρ hA hC ha hr, fun βb hβb hin => ?_⟩
  have hβO := ord_mem hcO hβb
  have h1 : piF P a ∈ Lev (ccF Q ρ) :=
    lev_sub_of_le (ord_sc hβO) hcO (ord_sc_le hβO hcO hβb) _ (inDef_mem hβO hin)
  obtain ⟨b, hb, hbL, e⟩ := (hA _).mp h1
  have e' := pi_inj cd.hd cd.hP a ha b hb e
  rw [← e'] at hbL
  exact mem_irrefl ρ ((rkL_mem hr hr.1).mp hbL)

include hρ hA hC in
theorem lex4_pi (u v : Fin 4 → V) (hu : ∀ i, u i ∈ N ∧ u i ∈ Lev ρ)
    (hv : ∀ i, v i ∈ N ∧ v i ∈ Lev ρ) :
    Lex4 (LtS ρ) (u 0) (u 1) (u 2) (u 3) (v 0) (v 1) (v 2) (v 3) ↔
      Lex4 (LtS (ccF Q ρ)) (piF P (u 0)) (piF P (u 1)) (piF P (u 2)) (piF P (u 3))
        (piF P (v 0)) (piF P (v 1)) (piF P (v 2)) (piF P (v 3)) := by
  have eq : ∀ i, (u i = v i ↔ piF P (u i) = piF P (v i)) := fun i =>
    ⟨fun h => by rw [h], pi_inj cd.hd cd.hP _ (hu i).1 _ (hv i).1⟩
  have lt : ∀ i, (Pr (LtS ρ) (u i) (v i) ↔ Pr (LtS (ccF Q ρ)) (piF P (u i)) (piF P (v i))) :=
    fun i => cd.lts_pi hρ hA hC (hu i).1 (hv i).1 (hu i).2 (hv i).2
  exact or_congr (lt 0) (and_congr (eq 0) (or_congr (lt 1) (and_congr (eq 1)
    (or_congr (lt 2) (and_congr (eq 2) (lt 3))))))

include hρ hA hC in
theorem pi_leastD {a s y₁ y₂ y₃ : V} (ha : a ∈ N) (hs : s ∈ N) (h1 : y₁ ∈ N) (h2 : y₂ ∈ N)
    (h3 : y₃ ∈ N) (hsL : s ∈ Lev ρ) (h1L : y₁ ∈ Lev ρ) (h2L : y₂ ∈ Lev ρ) (h3L : y₃ ∈ Lev ρ)
    (hL : LeastD (Lev ρ) (LtS ρ) s y₁ y₂ y₃ a) :
    LeastD (Lev (ccF Q ρ)) (LtS (ccF Q ρ)) (piF P s) (piF P y₁) (piF P y₂) (piF P y₃)
      (piF P a) := by
  refine ⟨cd.pi_isD hρ hA hC hs h1 h2 h3 ha hL.1,
    fun sb hsb y₁b h1b y₂b h2b y₃b h3b hDb hlex => ?_⟩
  obtain ⟨s', hs', hs'L, rfl⟩ := (hA sb).mp hsb
  obtain ⟨y₁', h1', h1'L, rfl⟩ := (hA y₁b).mp h1b
  obtain ⟨y₂', h2', h2'L, rfl⟩ := (hA y₂b).mp h2b
  obtain ⟨y₃', h3', h3'L, rfl⟩ := (hA y₃b).mp h3b
  obtain ⟨b, hDb'⟩ := exists_isD (Lev ρ) (LtS ρ) s' y₁' y₂' y₃'
  have hbN : b ∈ N := cd.hd.op_mem hρ.1 hρ.2 hs' h1' h2' h3' hs'L h1'L h2'L h3'L hDb'
  have hpb := cd.pi_isD hρ hA hC hs' h1' h2' h3' hbN hDb'
  have e : piF P b = piF P a := mem_ext (isD_ext hpb hDb)
  have e' : b = a := pi_inj cd.hd cd.hP b hbN a ha e
  rw [e'] at hDb'
  exact hL.2 s' hs'L y₁' h1'L y₂' h2'L y₃' h3'L hDb'
    ((cd.lex4_pi hρ hA hC ![s', y₁', y₂', y₃'] ![s, y₁, y₂, y₃]
      (fin4_all (p := fun x ↦ x ∈ N ∧ x ∈ Lev ρ) ⟨hs', hs'L⟩ ⟨h1', h1'L⟩ ⟨h2', h2'L⟩ ⟨h3', h3'L⟩)
      (fin4_all (p := fun x ↦ x ∈ N ∧ x ∈ Lev ρ) ⟨hs, hsL⟩ ⟨h1, h1L⟩ ⟨h2, h2L⟩
        ⟨h3, h3L⟩)).mpr hlex)

include hρ hA hC in
theorem sameless_pi {a b : V} (ha : a ∈ N) (hb : b ∈ N) (hra : RkL ρ a) (hrb : RkL ρ b) :
    SameLess (Lev ρ) (LtS ρ) a b ↔
      SameLess (Lev (ccF Q ρ)) (LtS (ccF Q ρ)) (piF P a) (piF P b) := by
  have hρO := hra.1
  have hw := wol hρO
  have hcO := cd.cc_ord hρ
  have hwc := wol hcO
  have eqL : ∀ a, a ∈ N → (a = Lev ρ ↔ piF P a = Lev (ccF Q ρ)) := fun a ha =>
    ⟨fun h => by rw [h]; exact cd.pi_lev hρ hA,
      fun h => pi_inj cd.hd cd.hP a ha _ hρ.2 (h.trans (cd.pi_lev hρ hA).symm)⟩
  have all4 : ∀ {s y₁ y₂ y₃ : V}, s ∈ N → y₁ ∈ N → y₂ ∈ N → y₃ ∈ N → s ∈ Lev ρ → y₁ ∈ Lev ρ →
      y₂ ∈ Lev ρ → y₃ ∈ Lev ρ →
      ∀ i : Fin 4, (![s, y₁, y₂, y₃] : Fin 4 → V) i ∈ N ∧ (![s, y₁, y₂, y₃] : Fin 4 → V) i ∈ Lev ρ :=
    fun a1 a2 a3 a4 b1 b2 b3 b4 =>
      fin4_all (p := fun x ↦ x ∈ N ∧ x ∈ Lev ρ) ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨a3, b3⟩ ⟨a4, b4⟩
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, s', hs', y₁', hy₁', y₂', hy₂',
      y₃', hy₃', hL, hL', hlex⟩)
    · exact Or.inl ⟨(eqL a ha).mp h1, fun h => h2 ((eqL b hb).mpr h)⟩
    · obtain ⟨hsN, h1N, h2N, h3N⟩ := cd.hd.ld_mem ha hra hs hy₁ hy₂ hy₃ hL
      obtain ⟨hsN', h1N', h2N', h3N'⟩ := cd.hd.ld_mem hb hrb hs' hy₁' hy₂' hy₃' hL'
      exact Or.inr ⟨fun h => h1 ((eqL a ha).mpr h), fun h => h2 ((eqL b hb).mpr h),
        _, pi_in hA hsN hs, _, pi_in hA h1N hy₁, _, pi_in hA h2N hy₂, _, pi_in hA h3N hy₃,
        _, pi_in hA hsN' hs', _, pi_in hA h1N' hy₁', _, pi_in hA h2N' hy₂', _,
        pi_in hA h3N' hy₃',
        cd.pi_leastD hρ hA hC ha hsN h1N h2N h3N hs hy₁ hy₂ hy₃ hL,
        cd.pi_leastD hρ hA hC hb hsN' h1N' h2N' h3N' hs' hy₁' hy₂' hy₃' hL',
        (cd.lex4_pi hρ hA hC ![s, y₁, y₂, y₃] ![s', y₁', y₂', y₃']
          (all4 hsN h1N h2N h3N hs hy₁ hy₂ hy₃)
          (all4 hsN' h1N' h2N' h3N' hs' hy₁' hy₂' hy₃')).mp hlex⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, sb, hsb, y₁b, hy₁b, y₂b, hy₂b, y₃b, hy₃b, sb', hsb', y₁b', hy₁b',
      y₂b', hy₂b', y₃b', hy₃b', hLb, hLb', hlex⟩)
    · exact Or.inl ⟨(eqL a ha).mpr h1, fun h => h2 ((eqL b hb).mp h)⟩
    · have hna : ¬a = Lev ρ := fun h => h1 ((eqL a ha).mp h)
      have hnb : ¬b = Lev ρ := fun h => h2 ((eqL b hb).mp h)
      obtain ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hL⟩ := leastD_exists hρO hw hra.2.1 hna
      obtain ⟨s', hs', y₁', hy₁', y₂', hy₂', y₃', hy₃', hL'⟩ :=
        leastD_exists hρO hw hrb.2.1 hnb
      obtain ⟨hsN, h1N, h2N, h3N⟩ := cd.hd.ld_mem ha hra hs hy₁ hy₂ hy₃ hL
      obtain ⟨hsN', h1N', h2N', h3N'⟩ := cd.hd.ld_mem hb hrb hs' hy₁' hy₂' hy₃' hL'
      have hp := cd.pi_leastD hρ hA hC ha hsN h1N h2N h3N hs hy₁ hy₂ hy₃ hL
      have hp' := cd.pi_leastD hρ hA hC hb hsN' h1N' h2N' h3N' hs' hy₁' hy₂' hy₃' hL'
      obtain ⟨e0, e1, e2, e3⟩ := leastD_unique hcO hwc hsb hy₁b hy₂b hy₃b (pi_in hA hsN hs)
        (pi_in hA h1N hy₁) (pi_in hA h2N hy₂) (pi_in hA h3N hy₃) hLb hp
      obtain ⟨f0, f1, f2, f3⟩ := leastD_unique hcO hwc hsb' hy₁b' hy₂b' hy₃b'
        (pi_in hA hsN' hs') (pi_in hA h1N' hy₁') (pi_in hA h2N' hy₂') (pi_in hA h3N' hy₃')
        hLb' hp'
      rw [e0, e1, e2, e3, f0, f1, f2, f3] at hlex
      exact Or.inr ⟨hna, hnb, s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, s', hs', y₁', hy₁', y₂', hy₂',
        y₃', hy₃', hL, hL',
        (cd.lex4_pi hρ hA hC ![s, y₁, y₂, y₃] ![s', y₁', y₂', y₃']
          (all4 hsN h1N h2N h3N hs hy₁ hy₂ hy₃)
          (all4 hsN' h1N' h2N' h3N' hs' hy₁' hy₂' hy₃')).mpr hlex⟩

omit hρ hA hC in
/-- **The step of the induction.** -/
theorem step {γ : V} (hγ : InS N δ' γ)
    (ih : ∀ ρ, ρ ∈ γ → Lev ρ ∈ N → StA N P Q ρ ∧ StC N P ρ) : StA N P Q γ ∧ StC N P γ := by
  have su := cd.hd.su
  have hγO := ord_mem su.ord hγ.1
  have hcO := cd.cc_ord hγ
  have hS : ∀ ρ, ρ ∈ γ → Lev ρ ∈ N → InS N δ' ρ := fun ρ h hN => cd.inS_of_mem hγ h hN
  have hA : StA N P Q γ := by
    intro z
    constructor
    · intro hz
      obtain ⟨βb, hβb, hin⟩ := (mem_lev hcO).mp hz
      obtain ⟨ρ, hρ, hρN, rfl⟩ := (cd.cc_mem hγ βb).mp hβb
      have hρS := hS ρ hρ hρN
      obtain ⟨hAρ, hCρ⟩ := ih ρ hρ hρN
      rcases hin with e | ⟨sb, hsb, y₁b, h1b, y₂b, h2b, y₃b, h3b, hDb⟩
      · exact ⟨Lev ρ, hρN, lev_mem hγO hρ, e.trans (cd.pi_lev hρS hAρ).symm⟩
      · obtain ⟨s, hs, hsL, rfl⟩ := (hAρ sb).mp hsb
        obtain ⟨y₁, h1, h1L, rfl⟩ := (hAρ y₁b).mp h1b
        obtain ⟨y₂, h2, h2L, rfl⟩ := (hAρ y₂b).mp h2b
        obtain ⟨y₃, h3, h3L, rfl⟩ := (hAρ y₃b).mp h3b
        obtain ⟨b, hDb'⟩ := exists_isD (Lev ρ) (LtS ρ) s y₁ y₂ y₃
        have hbN : b ∈ N := cd.hd.op_mem hρS.1 hρN hs h1 h2 h3 hsL h1L h2L h3L hDb'
        have hpb := cd.pi_isD hρS hAρ hCρ hs h1 h2 h3 hbN hDb'
        exact ⟨b, hbN, def_mem_lev hγO hρ hsL h1L h2L h3L hDb', mem_ext (isD_ext hDb hpb)⟩
    · rintro ⟨b, hbN, hbL, rfl⟩
      obtain ⟨ρ, hρ, hr⟩ := rkL_exists hγO hbL
      obtain ⟨-, hρN⟩ := cd.hd.rk_mem hbN hr
      have hρS := hS ρ hρ hρN
      obtain ⟨hAρ, hCρ⟩ := ih ρ hρ hρN
      exact (mem_lev hcO).mpr ⟨ccF Q ρ, (cd.cc_lt hρS hγ).mp hρ, cd.pi_inDef hρS hAρ hCρ hbN hr⟩
  refine ⟨hA, fun a b ha hb haL hbL => ?_⟩
  obtain ⟨ρa, hρa, hra⟩ := rkL_exists hγO haL
  obtain ⟨ρb, hρb, hrb⟩ := rkL_exists hγO hbL
  obtain ⟨-, hρaN⟩ := cd.hd.rk_mem ha hra
  obtain ⟨-, hρbN⟩ := cd.hd.rk_mem hb hrb
  have hSa := hS ρa hρa hρaN
  have hSb := hS ρb hρb hρbN
  obtain ⟨hAa, hCa⟩ := ih ρa hρa hρaN
  obtain ⟨hAb, hCb⟩ := ih ρb hρb hρbN
  rw [ltL_iff_rk hra hrb, ltL_iff_rk (cd.pi_rk hSa hAa hCa ha hra) (cd.pi_rk hSb hAb hCb hb hrb)]
  refine or_congr (cd.cc_lt hSa hSb) ?_
  constructor
  · rintro ⟨e, h⟩
    rw [← e] at hrb
    exact ⟨by rw [e], (cd.sameless_pi hSa hAa hCa ha hb hra hrb).mp h⟩
  · rintro ⟨e, h⟩
    have e' := cd.cc_inj hSa hSb e
    rw [← e'] at hrb
    exact ⟨e', (cd.sameless_pi hSa hAa hCa ha hb hra hrb).mpr h⟩

omit hρ hA hC in
/-- **The collapse maps the members of the hull in a level onto a level, and preserves the
order.** -/
theorem main_ind : ∀ γ, InS N δ' γ → StA N P Q γ ∧ StC N P γ := by
  have su := cd.hd.su
  have hκ : Ord (kap T) := ord_kap cd.trT
  obtain ⟨Fb, hFb⟩ := exists_hier hκ
  have conv : ∀ γ, InS N δ' γ →
      (GoodAt (Lev γ) (Lev (ccF Q γ)) N P (LtS δ') (LtS (kap T)) T ↔
        StA N P Q γ ∧ StC N P γ) := by
    intro γ hS
    have hcκ := cd.cc_kap hS
    have hsubκ : ∀ z, z ∈ Lev (ccF Q γ) → z ∈ Lev (kap T) := lev_mono hκ hcκ
    have hsubδ : ∀ z, z ∈ Lev γ → z ∈ Lev δ' := lev_mono su.ord hS.1
    constructor
    · rintro ⟨g1, g2, g3⟩
      have hA : StA N P Q γ := by
        intro z
        constructor
        · intro hz
          obtain ⟨b, hbL, hbN, hp⟩ := g1 z hz
          exact ⟨b, hbN, hbL, (piF_eq cd.hP hbN).mp hp⟩
        · rintro ⟨b, hbN, hbL, rfl⟩
          obtain ⟨z, hz, hp⟩ := g2 b hbL hbN
          rw [← (piF_eq cd.hP hbN).mp hp]
          exact hz
      refine ⟨hA, fun a b ha hb haL hbL => ?_⟩
      have h := g3 a haL b hbL ha hb (piF P a) (piF_mem cd.hP ha).1 (piF P b)
        (piF_mem cd.hP hb).1 ((piF_eq cd.hP ha).mpr rfl) ((piF_eq cd.hP hb).mpr rfl)
      rw [lts_iff su.ord, lts_iff hκ] at h
      have ha' : piF P a ∈ Lev (kap T) := hsubκ _ ((hA _).mpr ⟨a, ha, haL, rfl⟩)
      have hb' : piF P b ∈ Lev (kap T) := hsubκ _ ((hA _).mpr ⟨b, hb, hbL, rfl⟩)
      exact ⟨fun hl => (h.mp ⟨hsubδ a haL, hsubδ b hbL, hl⟩).2.2,
        fun hl => (h.mpr ⟨ha', hb', hl⟩).2.2⟩
    · rintro ⟨hA, hC⟩
      refine ⟨fun z hz => ?_, fun b hbL hbN => ?_,
        fun a haL b hbL ha hb ab _ bb _ hpa hpb => ?_⟩
      · obtain ⟨b, hbN, hbL, e⟩ := (hA z).mp hz
        exact ⟨b, hbL, hbN, (piF_eq cd.hP hbN).mpr e⟩
      · exact ⟨piF P b, (hA _).mpr ⟨b, hbN, hbL, rfl⟩, (piF_eq cd.hP hbN).mpr rfl⟩
      · have ea := (piF_eq cd.hP ha).mp hpa
        have eb := (piF_eq cd.hP hb).mp hpb
        rw [ea, eb, lts_iff su.ord, lts_iff hκ]
        have ha' : piF P a ∈ Lev (kap T) := hsubκ _ ((hA _).mpr ⟨a, ha, haL, rfl⟩)
        have hb' : piF P b ∈ Lev (kap T) := hsubκ _ ((hA _).mpr ⟨b, hb, hbL, rfl⟩)
        exact ⟨fun h => ⟨ha', hb', (hC a b ha hb haL hbL).mp h.2.2⟩,
          fun h => ⟨hsubδ a haL, hsubδ b hbL, (hC a b ha hb haL hbL).mpr h.2.2⟩⟩
  by_contra hcon
  let Z : V := sepB (k := 9) badB δ'
    ![N, F, T, Q, Lev (kap T), Fb, P, LtS δ', LtS (kap T)]
  have hZ : ∀ γ, γ ∈ Z ↔ γ ∈ δ' ∧ ∃ A, A ∈ N ∧ (LevAt F γ A ∧ ∃ αb, αb ∈ T ∧ (Pr Q A αb ∧
      ∃ Ab, Ab ∈ Lev (kap T) ∧ (LevAt Fb αb Ab ∧
        ¬GoodAt A Ab N P (LtS δ') (LtS (kap T)) T))) := fun γ => mem_sepB _ _ _ γ
  have hZ' : ∀ γ, γ ∈ Z ↔ InS N δ' γ ∧ ¬(StA N P Q γ ∧ StC N P γ) := by
    intro γ
    rw [hZ]
    constructor
    · rintro ⟨hγ, A, hA, hlev, αb, -, hq, Ab, -, hlevb, hn⟩
      have e1 := (su.levAt hγ).mp hlev
      rw [e1] at hA hq hn
      have hS : InS N δ' γ := ⟨hγ, hA⟩
      have e2 : αb = ccF Q γ := (piF_eq cd.hQ hA).mp hq
      rw [e2] at hlevb
      have e3 := (levAt_lev hκ hFb (mem_sc.mpr (Or.inr (cd.cc_kap hS)))).mp hlevb
      rw [e3] at hn
      exact ⟨hS, fun h => hn ((conv γ hS).mpr h)⟩
    · rintro ⟨hS, hn⟩
      exact ⟨hS.1, Lev γ, hS.2, (su.levAt hS.1).mpr rfl, ccF Q γ, cd.cc_T hS,
        (piF_eq cd.hQ hS.2).mpr rfl, Lev (ccF Q γ), lev_mem hκ (cd.cc_kap hS),
        (levAt_lev hκ hFb (mem_sc.mpr (Or.inr (cd.cc_kap hS)))).mpr rfl,
        fun h => hn ((conv γ hS).mp h)⟩
  have hne : ∃ γ, γ ∈ Z := by
    by_contra h
    refine hcon fun γ hS => ?_
    by_contra hn
    exact h ⟨γ, (hZ' γ).mpr ⟨hS, hn⟩⟩
  obtain ⟨γ, hγZ, hmin⟩ := ord_least Z (fun z hz => ord_mem su.ord ((hZ z).mp hz).1) hne
  obtain ⟨hS, hn⟩ := (hZ' γ).mp hγZ
  refine hn (cd.step hS fun ρ hρ hρN => ?_)
  by_contra hnρ
  rcases hmin ρ ((hZ' ρ).mpr ⟨cd.inS_of_mem hS hρ hρN, hnρ⟩) with e | e
  · rw [e] at hρ
    exact mem_irrefl ρ hρ
  · exact mem_asymm e hρ

end CollData

/-- **The bound**: for a big ordinal `ν` there is an ordinal `κ` such that every constructible
subset of the level at `ν` is a member of the level at `κ`. -/
theorem bound_exists {ν : V} (hν : Big ν) : ∃ κ : V, Ord κ ∧
    ∀ δ x : V, Ord δ → x ∈ Lev δ → (∀ z, z ∈ x → z ∈ Lev ν) → x ∈ Lev κ := by
  obtain ⟨T, hT⟩ := hc_of_models (V := V) (HCd (sc (sc (Lev ν))))
  refine ⟨kap T, ord_kap hT.1, fun δ x hδ hx hsub => ?_⟩
  obtain ⟨δ', hlim, hδδ', hνδ'⟩ := exists_lim2 hδ hν.1
  obtain ⟨F, hF⟩ := exists_hier hlim.1
  have su : Setup ν δ' F x := ⟨hν, hlim, hνδ', hF, lev_mono hlim.1 hδδ' x hx, hsub⟩
  obtain ⟨N, hd, hTN⟩ := exists_hull su hT
  obtain ⟨P, hP⟩ := hTN.2 (memR N) (wf_memR N)
  obtain ⟨Q, hQ⟩ := hTN.2 (levR N F (sc δ')) (wf_levR hd)
  have cd : CollData ν δ' F x N T P Q := ⟨hd, hT.1, hP, hQ⟩
  obtain ⟨ρ, hρ, hr⟩ := rkL_exists su.ord su.mem
  obtain ⟨-, hLρ⟩ := hd.rk_mem hd.gen3 hr
  have hS : InS N δ' ρ := ⟨hρ, hLρ⟩
  obtain ⟨hA, hC⟩ := cd.main_ind ρ hS
  have h1 := cd.pi_inDef hS hA hC hd.gen3 hr
  rw [cd.pi_x0] at h1
  have hcO := cd.cc_ord hS
  have h3 : x ∈ Lev (sc (ccF Q ρ)) := inDef_mem hcO h1
  exact lev_sub_of_le (ord_sc hcO) (ord_kap hT.1)
    (ord_sc_le hcO (ord_kap hT.1) (cd.cc_kap hS)) x h3

end cond

end MH

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.bound_exists
