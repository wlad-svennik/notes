import MHRec

set_option autoImplicit false

/-!
# The constructible levels

Inside a model `V` of `𝗠`. A level is a set `A` with a well-order `lt`. The next sets are the
level itself and the sets `{z ∈ A | Φ (z, s, y₁, y₂, y₃)}` for `s, y₁, y₂, y₃ ∈ A`, where `Φ` is
one fixed bounded condition: the first parameter `s` is a numeral that selects one of eight
operations (`PhiE` for the seven that use `∈` only; the eighth gives the pairs of the order
`lt` that are members of `A`).

* `IsD A lt s y₁ y₂ y₃ x`: `x = {z ∈ A | Φ}`. `InDef A lt x`: `x` is `A` or of this form.
* `GMain β f y`: the clause of the recursion. `y` is the pair of the level `A` and its order
  `lt` at stage `β`, given the earlier stages `f`: the members of `A` are the sets definable
  over an earlier level, and `lt` compares them first by the stage at which they appear, then
  with the level itself first, then by their least definitions.
* `IsHier F δ`: `F` is the sequence of the levels with their orders up to the ordinal `δ`.
  `hier_agree`: two such sequences agree where both are defined.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section defs

variable {V : Type} [SetStructure V]

/-- `s` is the numeral `n`. -/
def IsNum : ℕ → V → Prop
  | 0, s => ∀ w, w ∈ s → False
  | n + 1, s => ∃ m, m ∈ s ∧ (IsNum n m ∧ SuccR s m)

/-- `z` is a function from `k` to `t`. -/
def FunR (z k t : V) : Prop :=
  (∀ p, p ∈ z → ∃ i, i ∈ k ∧ ∃ a, a ∈ t ∧ IsOp p i a) ∧
  ((∀ i, i ∈ k → ∃ p, p ∈ z ∧ ∃ a, a ∈ t ∧ IsOp p i a) ∧
  (∀ p, p ∈ z → ∀ q, q ∈ z → ∀ i, i ∈ k → ∀ a, a ∈ t → ∀ b, b ∈ t →
    IsOp p i a → IsOp q i b → a = b))

/-- The value of `z` at `i` is a member of its value at `j`. -/
def MemAt (z i j : V) : Prop :=
  ∃ p, p ∈ z ∧ ∃ u, u ∈ p ∧ ∃ a, a ∈ u ∧ ∃ q, q ∈ z ∧ ∃ w, w ∈ q ∧ ∃ b, b ∈ w ∧
    (IsOp p i a ∧ (IsOp q j b ∧ a ∈ b))

/-- The value of `z` at `i` is its value at `j`. -/
def EqAt (z i j : V) : Prop :=
  ∃ p, p ∈ z ∧ ∃ u, u ∈ p ∧ ∃ a, a ∈ u ∧ (IsOp p i a ∧ Pr z j a)

/-- `p` is a pair with first component `j`. -/
def HasFst (p j : V) : Prop := ∃ u, u ∈ p ∧ ∃ a, a ∈ u ∧ IsOp p j a

/-- Every pair of `z` whose first component is not `j` is a member of `e`. -/
def AgreeOff (z e j : V) : Prop := ∀ p, p ∈ z → HasFst p j ∨ p ∈ e

/-- The seven operations that use `∈` only. -/
def PhiE (z s y₁ y₂ y₃ : V) : Prop :=
  (IsNum 0 s ∧ (z ∈ y₁ ∨ z = y₂)) ∨
  ((IsNum 1 s ∧ (z ∈ y₁ ∧ ¬z ∈ y₂)) ∨
  ((IsNum 2 s ∧ FunR z y₁ y₂) ∨
  ((IsNum 3 s ∧ (z ∈ y₁ ∧ MemAt z y₂ y₃)) ∨
  ((IsNum 4 s ∧ (z ∈ y₁ ∧ EqAt z y₂ y₃)) ∨
  ((IsNum 5 s ∧ (z ∈ y₁ ∧ ∃ e, e ∈ y₂ ∧ AgreeOff z e y₃)) ∨
  (IsNum 6 s ∧ ∃ e, e ∈ y₁ ∧ (Pr e y₃ z ∧ AgreeOff y₂ e y₃)))))))

/-- The condition `Φ`. The eighth operation gives the pairs of the order that are members of
the level. -/
def Phi (lt z s y₁ y₂ y₃ : V) : Prop := PhiE z s y₁ y₂ y₃ ∨ (IsNum 7 s ∧ z ∈ lt)

/-- `x = {z ∈ A | Φ (z, s, y₁, y₂, y₃)}` -/
def IsD (A lt s y₁ y₂ y₃ x : V) : Prop :=
  (∀ z, z ∈ x → z ∈ A ∧ Phi lt z s y₁ y₂ y₃) ∧ (∀ z, z ∈ A → Phi lt z s y₁ y₂ y₃ → z ∈ x)

/-- `x` is `A`, or definable over `A` with parameters in `A`. -/
def InDef (A lt x : V) : Prop :=
  x = A ∨ ∃ s, s ∈ A ∧ ∃ y₁, y₁ ∈ A ∧ ∃ y₂, y₂ ∈ A ∧ ∃ y₃, y₃ ∈ A ∧ IsD A lt s y₁ y₂ y₃ x

/-- `x` is definable over the level of `f` at `β`. -/
def InDefAt (f β x : V) : Prop :=
  ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ d ∧
    ∃ lt, lt ∈ w' ∧ (IsOp q β d ∧ (IsOp d A lt ∧ InDef A lt x))

/-- `x` appears first at stage `β`. -/
def RkAt (f β x : V) : Prop := InDefAt f β x ∧ ∀ β', β' ∈ β → ¬InDefAt f β' x

/-- The lexicographic order of four-tuples. -/
def Lex4 (lt a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : V) : Prop :=
  Pr lt a₀ b₀ ∨ (a₀ = b₀ ∧ (Pr lt a₁ b₁ ∨ (a₁ = b₁ ∧ (Pr lt a₂ b₂ ∨ (a₂ = b₂ ∧ Pr lt a₃ b₃)))))

/-- `(s, y₁, y₂, y₃)` is the least definition of `x` over `A`. -/
def LeastD (A lt s y₁ y₂ y₃ x : V) : Prop :=
  IsD A lt s y₁ y₂ y₃ x ∧ ∀ s', s' ∈ A → ∀ y₁', y₁' ∈ A → ∀ y₂', y₂' ∈ A → ∀ y₃', y₃' ∈ A →
    IsD A lt s' y₁' y₂' y₃' x → ¬Lex4 lt s' y₁' y₂' y₃' s y₁ y₂ y₃

/-- The order of the sets that appear first over `A`: `A` itself, then by least definitions. -/
def SameLess (A lt x x' : V) : Prop :=
  (x = A ∧ ¬x' = A) ∨ (¬x = A ∧ (¬x' = A ∧
    ∃ s, s ∈ A ∧ ∃ y₁, y₁ ∈ A ∧ ∃ y₂, y₂ ∈ A ∧ ∃ y₃, y₃ ∈ A ∧
    ∃ s', s' ∈ A ∧ ∃ y₁', y₁' ∈ A ∧ ∃ y₂', y₂' ∈ A ∧ ∃ y₃', y₃' ∈ A ∧
      (LeastD A lt s y₁ y₂ y₃ x ∧ (LeastD A lt s' y₁' y₂' y₃' x' ∧
        Lex4 lt s y₁ y₂ y₃ s' y₁' y₂' y₃'))))

/-- `SameLess` over the level of `f` at `β`. -/
def SameAt (f β x x' : V) : Prop :=
  ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ d ∧
    ∃ lt, lt ∈ w' ∧ (IsOp q β d ∧ (IsOp d A lt ∧ SameLess A lt x x'))

/-- The order of the sets that appear before stage `β`. -/
def KeyLess (f β x x' : V) : Prop :=
  ∃ β₁, β₁ ∈ β ∧ ∃ β₂, β₂ ∈ β ∧ (RkAt f β₁ x ∧ (RkAt f β₂ x' ∧
    (β₁ ∈ β₂ ∨ (β₁ = β₂ ∧ SameAt f β₁ x x'))))

/-- `A` contains the level of `f` at `β` and everything definable over it. -/
def CloseAt (f β A : V) : Prop :=
  ∀ q, q ∈ f → ∀ u, u ∈ q → ∀ d, d ∈ u → ∀ w, w ∈ d → ∀ A', A' ∈ w → ∀ w', w' ∈ d →
    ∀ lt', lt' ∈ w' → IsOp q β d → IsOp d A' lt' →
      (A' ∈ A ∧ ∀ s, s ∈ A' → ∀ y₁, y₁ ∈ A' → ∀ y₂, y₂ ∈ A' → ∀ y₃, y₃ ∈ A' →
        ∃ x, x ∈ A ∧ IsD A' lt' s y₁ y₂ y₃ x)

/-- **The clause of the recursion.** -/
def GMain (β f y : V) : Prop :=
  ∃ w, w ∈ y ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ y ∧ ∃ lt, lt ∈ w' ∧ (IsOp y A lt ∧
    ((∀ x, x ∈ A → ∃ β', β' ∈ β ∧ InDefAt f β' x) ∧
    ((∀ β', β' ∈ β → CloseAt f β' A) ∧
    ((∀ q, q ∈ lt → ∃ x, x ∈ A ∧ ∃ x', x' ∈ A ∧ IsOp q x x') ∧
    (∀ x, x ∈ A → ∀ x', x' ∈ A → (Pr lt x x' ↔ KeyLess f β x x'))))))

end defs

/-! ### Bounded definitions -/

def isNumB : (n : ℕ) → BDef (k := 1) (fun V _ v ↦ IsNum n (v 0))
  | 0 => (BDef.ball 0 BDef.fls).congr fun _ _ _ => Iff.rfl
  | n + 1 => (BDef.bex 0 (((isNumB n).comp ![0]).and (succB.comp ![1, 0]))).congr
      fun _ _ _ => Iff.rfl

def funRB : BDef (k := 3) (fun V _ v ↦ FunR (v 0) (v 1) (v 2)) :=
  ((BDef.ball 0 (BDef.bex 2 (BDef.bex 4 (isOpB.comp ![2, 1, 0])))).and
    ((BDef.ball 1 (BDef.bex 1 (BDef.bex 4 (isOpB.comp ![1, 2, 0])))).and
    (BDef.ball 0 (BDef.ball 1 (BDef.ball 3 (BDef.ball 5 (BDef.ball 6
      ((isOpB.comp ![4, 2, 1]).imp ((isOpB.comp ![3, 2, 0]).imp (BDef.eq 1 0)))))))))).congr
    fun _ _ _ => Iff.rfl

def memAtB : BDef (k := 3) (fun V _ v ↦ MemAt (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 3 (BDef.bex 0 (BDef.bex 0
    ((isOpB.comp ![5, 7, 3]).and ((isOpB.comp ![2, 8, 0]).and (BDef.mem 3 0))))))))).congr
    fun _ _ _ => Iff.rfl

def eqAtB : BDef (k := 3) (fun V _ v ↦ EqAt (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0
    ((isOpB.comp ![2, 4, 0]).and (prB.comp ![3, 5, 0]))))).congr fun _ _ _ => Iff.rfl

def hasFstB : BDef (k := 2) (fun V _ v ↦ HasFst (v 0) (v 1)) :=
  (BDef.bex 0 (BDef.bex 0 (isOpB.comp ![2, 3, 0]))).congr fun _ _ _ => Iff.rfl

def agreeOffB : BDef (k := 3) (fun V _ v ↦ AgreeOff (v 0) (v 1) (v 2)) :=
  (BDef.ball 0 ((hasFstB.comp ![0, 3]).or (BDef.mem 0 2))).congr fun _ _ _ => Iff.rfl

def phiEB : BDef (k := 5) (fun V _ v ↦ PhiE (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((((isNumB 0).comp ![1]).and ((BDef.mem 0 2).or (BDef.eq 0 3))).or
  ((((isNumB 1).comp ![1]).and ((BDef.mem 0 2).and (BDef.mem 0 3).not)).or
  ((((isNumB 2).comp ![1]).and (funRB.comp ![0, 2, 3])).or
  ((((isNumB 3).comp ![1]).and ((BDef.mem 0 2).and (memAtB.comp ![0, 3, 4]))).or
  ((((isNumB 4).comp ![1]).and ((BDef.mem 0 2).and (eqAtB.comp ![0, 3, 4]))).or
  ((((isNumB 5).comp ![1]).and ((BDef.mem 0 2).and
    (BDef.bex 3 (agreeOffB.comp ![1, 0, 5])))).or
  (((isNumB 6).comp ![1]).and (BDef.bex 2 ((prB.comp ![0, 5, 1]).and
    (agreeOffB.comp ![4, 0, 5])))))))))).congr fun _ _ _ => Iff.rfl

def phiB : BDef (k := 6) (fun V _ v ↦ Phi (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  ((phiEB.comp ![1, 2, 3, 4, 5]).or (((isNumB 7).comp ![2]).and (BDef.mem 1 0))).congr
    fun _ _ _ => Iff.rfl

def isDB : BDef (k := 7) (fun V _ v ↦ IsD (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  ((BDef.ball 6 ((BDef.mem 0 1).and (phiB.comp ![2, 0, 3, 4, 5, 6]))).and
    (BDef.ball 0 ((phiB.comp ![2, 0, 3, 4, 5, 6]).imp (BDef.mem 0 7)))).congr
    fun _ _ _ => Iff.rfl

def inDefB : BDef (k := 3) (fun V _ v ↦ InDef (v 0) (v 1) (v 2)) :=
  ((BDef.eq 2 0).or (BDef.bex 0 (BDef.bex 1 (BDef.bex 2 (BDef.bex 3
    (isDB.comp ![4, 5, 3, 2, 1, 0, 6])))))).congr fun _ _ _ => Iff.rfl

def inDefAtB : BDef (k := 3) (fun V _ v ↦ InDefAt (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0
    ((isOpB.comp ![6, 8, 4]).and ((isOpB.comp ![4, 2, 0]).and
      (inDefB.comp ![2, 0, 9])))))))))).congr fun _ _ _ => Iff.rfl

def rkAtB : BDef (k := 3) (fun V _ v ↦ RkAt (v 0) (v 1) (v 2)) :=
  ((inDefAtB.comp ![0, 1, 2]).and (BDef.ball 1 (inDefAtB.comp ![1, 0, 3]).not)).congr
    fun _ _ _ => Iff.rfl

def lex4B : BDef (k := 9)
    (fun V _ v ↦ Lex4 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  ((prB.comp ![0, 1, 5]).or ((BDef.eq 1 5).and ((prB.comp ![0, 2, 6]).or ((BDef.eq 2 6).and
    ((prB.comp ![0, 3, 7]).or ((BDef.eq 3 7).and (prB.comp ![0, 4, 8]))))))).congr
    fun _ _ _ => Iff.rfl

def leastDB : BDef (k := 7) (fun V _ v ↦ LeastD (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  ((isDB.comp ![0, 1, 2, 3, 4, 5, 6]).and (BDef.ball 0 (BDef.ball 1 (BDef.ball 2 (BDef.ball 3
    ((isDB.comp ![4, 5, 3, 2, 1, 0, 10]).imp
      (lex4B.comp ![5, 3, 2, 1, 0, 6, 7, 8, 9]).not)))))).congr fun _ _ _ => Iff.rfl

def sameLessB : BDef (k := 4) (fun V _ v ↦ SameLess (v 0) (v 1) (v 2) (v 3)) :=
  (((BDef.eq 2 0).and (BDef.eq 3 0).not).or ((BDef.eq 2 0).not.and ((BDef.eq 3 0).not.and
    (BDef.bex 0 (BDef.bex 1 (BDef.bex 2 (BDef.bex 3 (BDef.bex 4 (BDef.bex 5 (BDef.bex 6
      (BDef.bex 7 ((leastDB.comp ![8, 9, 7, 6, 5, 4, 10]).and
        ((leastDB.comp ![8, 9, 3, 2, 1, 0, 11]).and
          (lex4B.comp ![9, 7, 6, 5, 4, 3, 2, 1, 0])))))))))))))).congr fun _ _ _ => Iff.rfl

def sameAtB : BDef (k := 4) (fun V _ v ↦ SameAt (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0
    ((isOpB.comp ![6, 8, 4]).and ((isOpB.comp ![4, 2, 0]).and
      (sameLessB.comp ![2, 0, 9, 10])))))))))).congr fun _ _ _ => Iff.rfl

def keyLessB : BDef (k := 4) (fun V _ v ↦ KeyLess (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 1 (BDef.bex 2 ((rkAtB.comp ![2, 1, 4]).and ((rkAtB.comp ![2, 0, 5]).and
    ((BDef.mem 1 0).or ((BDef.eq 1 0).and (sameAtB.comp ![2, 1, 4, 5]))))))).congr
    fun _ _ _ => Iff.rfl

def closeAtB : BDef (k := 3) (fun V _ v ↦ CloseAt (v 0) (v 1) (v 2)) :=
  (BDef.ball 0 (BDef.ball 0 (BDef.ball 0 (BDef.ball 0 (BDef.ball 0 (BDef.ball 2 (BDef.ball 0
    ((isOpB.comp ![6, 8, 4]).imp ((isOpB.comp ![4, 2, 0]).imp ((BDef.mem 2 9).and
      (BDef.ball 2 (BDef.ball 3 (BDef.ball 4 (BDef.ball 5 (BDef.bex 13
        (isDB.comp ![7, 5, 4, 3, 2, 1, 0])))))))))))))))).congr fun _ _ _ => Iff.rfl

def gMainB : BDef (k := 3) (fun V _ v ↦ GMain (v 0) (v 1) (v 2)) :=
  (BDef.bex 2 (BDef.bex 0 (BDef.bex 4 (BDef.bex 0 ((isOpB.comp ![6, 2, 0]).and
    ((BDef.ball 2 (BDef.bex 5 (inDefAtB.comp ![7, 0, 1]))).and
    ((BDef.ball 4 (closeAtB.comp ![6, 0, 3])).and
    ((BDef.ball 0 (BDef.bex 3 (BDef.bex 4 (isOpB.comp ![2, 1, 0])))).and
    (BDef.ball 2 (BDef.ball 3 ((prB.comp ![2, 1, 0]).iff
      (keyLessB.comp ![7, 6, 1, 0])))))))))))).congr fun _ _ _ => Iff.rfl

/-! ### What the definitions say -/

section bridge

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem exAt_iff {f β : V} {P : V → V → Prop} :
    (∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ d ∧
      ∃ lt, lt ∈ w' ∧ (IsOp q β d ∧ (IsOp d A lt ∧ P A lt))) ↔
    ∃ A lt, Pr f β (kp A lt) ∧ P A lt := by
  constructor
  · rintro ⟨q, hq, u, -, d, -, w, -, A, -, w', -, lt, -, h1, h2, h3⟩
    have e := isOp_iff.mp h2
    subst e
    exact ⟨A, lt, ⟨q, hq, h1⟩, h3⟩
  · rintro ⟨A, lt, ⟨q, hq, hop⟩, hP⟩
    obtain ⟨u, hu, hdu⟩ := pr_snd_mem hop
    obtain ⟨w, hw, hAw⟩ := pr_fst_mem (isOp_kp A lt)
    obtain ⟨w', hw', hlw⟩ := pr_snd_mem (isOp_kp A lt)
    exact ⟨q, hq, u, hu, kp A lt, hdu, w, hw, A, hAw, w', hw', lt, hlw, hop, isOp_kp A lt, hP⟩

theorem inDefAt_iff {f β x : V} :
    InDefAt f β x ↔ ∃ A lt, Pr f β (kp A lt) ∧ InDef A lt x := exAt_iff

theorem sameAt_iff {f β x x' : V} :
    SameAt f β x x' ↔ ∃ A lt, Pr f β (kp A lt) ∧ SameLess A lt x x' := exAt_iff

theorem closeAt_iff {f β A : V} :
    CloseAt f β A ↔ ∀ A' lt', Pr f β (kp A' lt') →
      (A' ∈ A ∧ ∀ s, s ∈ A' → ∀ y₁, y₁ ∈ A' → ∀ y₂, y₂ ∈ A' → ∀ y₃, y₃ ∈ A' →
        ∃ x, x ∈ A ∧ IsD A' lt' s y₁ y₂ y₃ x) := by
  constructor
  · rintro h A' lt' ⟨q, hq, hop⟩
    obtain ⟨u, hu, hdu⟩ := pr_snd_mem hop
    obtain ⟨w, hw, hAw⟩ := pr_fst_mem (isOp_kp A' lt')
    obtain ⟨w', hw', hlw⟩ := pr_snd_mem (isOp_kp A' lt')
    exact h q hq u hu (kp A' lt') hdu w hw A' hAw w' hw' lt' hlw hop (isOp_kp A' lt')
  · intro h q hq u _ d _ w _ A' _ w' _ lt' _ h1 h2
    have e := isOp_iff.mp h2
    subst e
    exact h A' lt' ⟨q, hq, h1⟩

theorem gMain_iff {β f y : V} :
    GMain β f y ↔ ∃ A lt, y = kp A lt ∧
      ((∀ x, x ∈ A → ∃ β', β' ∈ β ∧ InDefAt f β' x) ∧
      ((∀ β', β' ∈ β → CloseAt f β' A) ∧
      ((∀ q, q ∈ lt → ∃ x, x ∈ A ∧ ∃ x', x' ∈ A ∧ IsOp q x x') ∧
      (∀ x, x ∈ A → ∀ x', x' ∈ A → (Pr lt x x' ↔ KeyLess f β x x'))))) := by
  constructor
  · rintro ⟨w, -, A, -, w', -, lt, -, hop, h⟩
    exact ⟨A, lt, isOp_iff.mp hop, h⟩
  · rintro ⟨A, lt, rfl, h⟩
    obtain ⟨w, hw, hAw⟩ := pr_fst_mem (isOp_kp A lt)
    obtain ⟨w', hw', hlw⟩ := pr_snd_mem (isOp_kp A lt)
    exact ⟨w, hw, A, hAw, w', hw', lt, hlw, isOp_kp A lt, h⟩

/-! ### The clause depends only on the earlier stages, and determines the level -/

theorem inDefAt_congr {f f' β x : V} (h : ∀ d, Pr f β d ↔ Pr f' β d) :
    InDefAt f β x ↔ InDefAt f' β x := by
  simp only [inDefAt_iff, h]

theorem sameAt_congr {f f' β x x' : V} (h : ∀ d, Pr f β d ↔ Pr f' β d) :
    SameAt f β x x' ↔ SameAt f' β x x' := by
  simp only [sameAt_iff, h]

theorem closeAt_congr {f f' β A : V} (h : ∀ d, Pr f β d ↔ Pr f' β d) :
    CloseAt f β A ↔ CloseAt f' β A := by
  simp only [closeAt_iff, h]

theorem rkAt_congr {f f' β x : V} (h : ∀ d, Pr f β d ↔ Pr f' β d)
    (hb : ∀ β', β' ∈ β → ∀ d, Pr f β' d ↔ Pr f' β' d) : RkAt f β x ↔ RkAt f' β x :=
  and_congr (inDefAt_congr h) (forall_congr' fun β' => imp_congr_right fun hβ' =>
    not_congr (inDefAt_congr (hb β' hβ')))

theorem keyLess_congr {f f' γ x x' : V} (hγ : Ord γ)
    (h : ∀ γ', γ' ∈ γ → ∀ d, Pr f γ' d ↔ Pr f' γ' d) : KeyLess f γ x x' ↔ KeyLess f' γ x x' := by
  refine exists_congr fun β₁ => and_congr_right fun h1 => exists_congr fun β₂ =>
    and_congr_right fun h2 => ?_
  have hb1 : ∀ β', β' ∈ β₁ → ∀ d, Pr f β' d ↔ Pr f' β' d := fun β' hβ' =>
    h β' (hγ.1 β₁ h1 β' hβ')
  have hb2 : ∀ β', β' ∈ β₂ → ∀ d, Pr f β' d ↔ Pr f' β' d := fun β' hβ' =>
    h β' (hγ.1 β₂ h2 β' hβ')
  exact and_congr (rkAt_congr (h β₁ h1) hb1) (and_congr (rkAt_congr (h β₂ h2) hb2)
    (or_congr Iff.rfl (and_congr Iff.rfl (sameAt_congr (h β₁ h1)))))

theorem gMain_loc (γ f f' y : V) (hγ : Ord γ)
    (h : ∀ γ', γ' ∈ γ → ∀ d, Pr f γ' d ↔ Pr f' γ' d) (hG : GMain γ f y) : GMain γ f' y := by
  obtain ⟨A, lt, rfl, ha, hb, hc, hd⟩ := gMain_iff.mp hG
  refine gMain_iff.mpr ⟨A, lt, rfl, fun x hx => ?_, fun β' hβ' => ?_, hc, fun x hx x' hx' => ?_⟩
  · obtain ⟨β', hβ', hx'⟩ := ha x hx
    exact ⟨β', hβ', (inDefAt_congr (h β' hβ')).mp hx'⟩
  · exact (closeAt_congr (h β' hβ')).mp (hb β' hβ')
  · exact (hd x hx x' hx').trans (keyLess_congr hγ h)

omit [Nonempty V] hV in
theorem isD_ext {A lt s y₁ y₂ y₃ x x' : V} (h : IsD A lt s y₁ y₂ y₃ x)
    (h' : IsD A lt s y₁ y₂ y₃ x') : ∀ z, z ∈ x ↔ z ∈ x' := fun z =>
  ⟨fun hz => h'.2 z (h.1 z hz).1 (h.1 z hz).2, fun hz => h.2 z (h'.1 z hz).1 (h'.1 z hz).2⟩

theorem gMain_uniq (γ f y y' : V) (hG : GMain γ f y) (hG' : GMain γ f y') : y = y' := by
  obtain ⟨A, lt, rfl, ha, hb, hc, hd⟩ := gMain_iff.mp hG
  obtain ⟨A', lt', rfl, ha', hb', hc', hd'⟩ := gMain_iff.mp hG'
  have key : ∀ (A A' : V), (∀ x, x ∈ A → ∃ β', β' ∈ γ ∧ InDefAt f β' x) →
      (∀ β', β' ∈ γ → CloseAt f β' A') → ∀ x, x ∈ A → x ∈ A' := by
    intro A A' ha hb' x hx
    obtain ⟨β', hβ', hx'⟩ := ha x hx
    obtain ⟨A₁, lt₁, hf, hin⟩ := inDefAt_iff.mp hx'
    obtain ⟨hA₁, hcl⟩ := closeAt_iff.mp (hb' β' hβ') A₁ lt₁ hf
    rcases hin with rfl | ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩
    · exact hA₁
    · obtain ⟨x', hx'A, hD'⟩ := hcl s hs y₁ hy₁ y₂ hy₂ y₃ hy₃
      rw [mem_ext (isD_ext hD hD')]
      exact hx'A
  have eA : A = A' := mem_ext fun x => ⟨key A A' ha hb' x, key A' A ha' hb x⟩
  subst eA
  have elt : lt = lt' := mem_ext fun q => by
    constructor
    · intro hq
      obtain ⟨x, hx, x', hx', hop⟩ := hc q hq
      obtain ⟨q', hq', hop'⟩ := (hd' x hx x' hx').mpr ((hd x hx x' hx').mp ⟨q, hq, hop⟩)
      rw [isOp_iff.mp hop, ← isOp_iff.mp hop']
      exact hq'
    · intro hq
      obtain ⟨x, hx, x', hx', hop⟩ := hc' q hq
      obtain ⟨q', hq', hop'⟩ := (hd x hx x' hx').mpr ((hd' x hx x' hx').mp ⟨q, hq, hop⟩)
      rw [isOp_iff.mp hop, ← isOp_iff.mp hop']
      exact hq'
  rw [elt]

end bridge

/-! ### The sequence of the levels -/

/-- The clause as a relation of three arguments. -/
def GMainR : MRel 3 := fun V _ v ↦ GMain (v 0) (v 1) (v 2)

section hier

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- `F` is the sequence of the levels, with their orders, at the stages `≤ δ`. -/
def IsHier (F δ : V) : Prop := IsAtt (k := 0) GMainR ![] F (sc δ)

theorem gMainR_loc : ∀ γ f f' y : V, Ord γ → (∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y') →
    GMainR V (γ :> f :> y :> ![]) → GMainR V (γ :> f' :> y :> ![]) :=
  fun γ f f' y hγ h hG => gMain_loc γ f f' y hγ h hG

theorem gMainR_uniq : ∀ γ f y y' : V, GMainR V (γ :> f :> y :> ![]) →
    GMainR V (γ :> f :> y' :> ![]) → y = y' :=
  fun γ f y y' hG hG' => gMain_uniq γ f y y' hG hG'

/-- **Two sequences of levels agree where both are defined.** -/
theorem hier_agree {F F' δ δ' γ : V} (hδ : Ord δ) (hδ' : Ord δ') (hF : IsHier F δ)
    (hF' : IsHier F' δ') (hγ : γ ∈ sc δ) (hγ' : γ ∈ sc δ') (y : V) : Pr F γ y ↔ Pr F' γ y :=
  att_agree_iff gMainR_loc gMainR_uniq (ord_sc hδ) (ord_sc hδ') hF hF' hγ hγ' y

theorem hier_at {F δ γ : V} (hF : IsHier F δ) (hγ : γ ∈ sc δ) :
    ∃ A lt, Pr F γ (kp A lt) ∧
      ((∀ x, x ∈ A → ∃ β', β' ∈ γ ∧ InDefAt F β' x) ∧
      ((∀ β', β' ∈ γ → CloseAt F β' A) ∧
      ((∀ q, q ∈ lt → ∃ x, x ∈ A ∧ ∃ x', x' ∈ A ∧ IsOp q x x') ∧
      (∀ x, x ∈ A → ∀ x', x' ∈ A → (Pr lt x x' ↔ KeyLess F γ x x'))))) := by
  obtain ⟨y, hy, hG⟩ := att_total hF hγ
  obtain ⟨A, lt, rfl, h⟩ := gMain_iff.mp hG
  exact ⟨A, lt, hy, h⟩

theorem hier_fun {F δ γ A lt A' lt' : V} (hF : IsHier F δ) (h : Pr F γ (kp A lt))
    (h' : Pr F γ (kp A' lt')) : A = A' ∧ lt = lt' := kp_inj (att_fun hF h h')

end hier

end MH

end FFL.FirstOrder.SetTheory
