import MDefs

set_option autoImplicit false

/-!
# Mac Lane set theory with the collapse axiom

`𝗠𝗛` is `𝗠` (Mathias's theory: Mac Lane set theory with transitive containment and without
choice) together with the **collapse axiom**:

> for every set `u` there is a transitive set `T` such that every well-founded relation `r` on
> `u` has a collapse into `T`: a function `F` from `u` to `T` with
> `F(b) = {F(a) : a ∈ u, a r b}` for every `b ∈ u`.

The relation need not be extensional, and the bound `T` depends only on `u`. Over `𝗠` this is a
form of Mathias's axiom H (for every `u` there is a transitive set that includes every
transitive set of size at most that of `u`); the equivalence is not proved here.

* `MH.IsOp p a b`: `p` is the Kuratowski pair of `a` and `b`. `MH.Pr r a b`: the pair is a
  member of `r`.
* `MH.HC V`: the collapse axiom holds in the structure `V`.
* `Axiom.collapse`, `𝗠𝗛`.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section defs

variable {V : Type} [SetStructure V]

/-- `u = {a}` -/
def IsSing (u a : V) : Prop := a ∈ u ∧ ∀ c, c ∈ u → c = a

/-- `u = {a, b}` -/
def IsUp (u a b : V) : Prop := a ∈ u ∧ b ∈ u ∧ ∀ c, c ∈ u → c = a ∨ c = b

/-- `p = ⟨a, b⟩`, the Kuratowski pair. -/
def IsOp (p a b : V) : Prop :=
  (∃ s, s ∈ p ∧ IsSing s a) ∧ (∃ d, d ∈ p ∧ IsUp d a b) ∧
    ∀ z, z ∈ p → IsSing z a ∨ IsUp z a b

/-- `⟨a, b⟩ ∈ r` -/
def Pr (r a b : V) : Prop := ∃ p, p ∈ r ∧ IsOp p a b

/-- `T` is transitive. -/
def Tr (T : V) : Prop := ∀ y, y ∈ T → ∀ z, z ∈ y → z ∈ T

/-- `r` is well-founded on `u`: every subset of `u` with a member has a member with no
predecessor in the subset. -/
def WFon (r u : V) : Prop :=
  ∀ X : V, (∃ c, c ∈ X ∧ ¬False) → (∀ c, c ∈ X → c ∈ u) → ∃ c, c ∈ X ∧ ∀ b, b ∈ X → ¬Pr r b c

/-- `F` is a collapse of `r` on `u` with values in `T`. -/
def IsColl (F r u T : V) : Prop :=
  ∀ b, b ∈ u → ∃ v, v ∈ T ∧ Pr F b v ∧ (∀ v', Pr F b v' → v' = v) ∧
    ∀ y, (y ∈ v ↔ ∃ a, a ∈ u ∧ Pr r a b ∧ Pr F a y)

/-- `T` is transitive and every well-founded relation on `u` has a collapse into `T`. -/
def HCat (T u : V) : Prop := Tr T ∧ ∀ r : V, WFon r u → ∃ F : V, IsColl F r u T

end defs

/-- **The collapse axiom** in a structure. -/
def HC (V : Type) [SetStructure V] : Prop := ∀ u : V, ∃ T : V, HCat T u

/-! ### Formulas -/

def isSingB : BDef (k := 2) (fun V _ v ↦ IsSing (v 0) (v 1)) :=
  ((BDef.mem 1 0).and (BDef.ball 0 (BDef.eq 0 2))).congr fun _ _ _ => Iff.rfl

def isUpB : BDef (k := 3) (fun V _ v ↦ IsUp (v 0) (v 1) (v 2)) :=
  ((BDef.mem 1 0).and ((BDef.mem 2 0).and
    (BDef.ball 0 ((BDef.eq 0 2).or (BDef.eq 0 3))))).congr fun _ _ _ => Iff.rfl

def isOpB : BDef (k := 3) (fun V _ v ↦ IsOp (v 0) (v 1) (v 2)) :=
  ((BDef.bex 0 (isSingB.comp ![0, 2])).and ((BDef.bex 0 (isUpB.comp ![0, 2, 3])).and
    (BDef.ball 0 ((isSingB.comp ![0, 2]).or (isUpB.comp ![0, 2, 3]))))).congr
    fun _ _ _ => Iff.rfl

def prB : BDef (k := 3) (fun V _ v ↦ Pr (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (isOpB.comp ![0, 2, 3])).congr fun _ _ _ => Iff.rfl

def trB : BDef (k := 1) (fun V _ v ↦ Tr (v 0)) :=
  (BDef.ball 0 (BDef.ball 0 (BDef.mem 0 2))).congr fun _ _ _ => Iff.rfl

def wfonF : FDef (k := 2) (fun V _ v ↦ WFon (v 0) (v 1)) :=
  (FDef.all (((BDef.bex 0 BDef.fls.not).imp ((BDef.ball 0 (BDef.mem 0 3)).imp
    (BDef.bex 0 (BDef.ball 1 (prB.comp ![3, 0, 1]).not)))).toFDef)).congr
    fun _ _ _ => Iff.rfl

def isCollF : FDef (k := 4) (fun V _ v ↦ IsColl (v 0) (v 1) (v 2) (v 3)) :=
  (FDef.all ((BDef.mem 0 3).toFDef.imp (FDef.ex ((BDef.mem 0 5).toFDef.and
    ((prB.comp ![2, 1, 0]).toFDef.and
      ((FDef.all ((prB.comp ![3, 2, 0]).toFDef.imp (BDef.eq 0 1).toFDef)).and
        (FDef.all ((BDef.mem 0 1).toFDef.iff
          (BDef.bex 5 ((prB.comp ![5, 0, 3]).and (prB.comp ![4, 0, 1]))).toFDef)))))))).congr
    fun _ _ _ => Iff.rfl

def hcatF : FDef (k := 2) (fun V _ v ↦ HCat (v 0) (v 1)) :=
  ((trB.comp ![0]).toFDef.and (FDef.all ((wfonF.comp ![0, 2]).imp
    (FDef.ex (isCollF.comp ![0, 1, 3, 2]))))).congr fun _ _ _ => Iff.rfl

def hcF : FDef (k := 0) (fun V _ _ ↦ HC V) :=
  (FDef.all (FDef.ex (hcatF.comp ![0, 1]))).congr fun _ _ _ => Iff.rfl

/-! ### Pairs: what follows by logic alone -/

section pairs

variable {V : Type} [SetStructure V]

theorem sing_inj {s a a' : V} (h : IsSing s a) (h' : IsSing s a') : a = a' := h'.2 a h.1

theorem op_inj {p a b a' b' : V} (h : IsOp p a b) (h' : IsOp p a' b') : a = a' ∧ b = b' := by
  obtain ⟨⟨s, hs, hsa⟩, ⟨d, hd, hdab⟩, hall⟩ := h
  obtain ⟨⟨s', hs', hsa'⟩, ⟨d', hd', hdab'⟩, hall'⟩ := h'
  have e : a = a' := by
    rcases hall' s hs with h1 | h1
    · exact sing_inj hsa h1
    · exact (hsa.2 a' h1.1).symm
  subst e
  refine ⟨rfl, ?_⟩
  rcases hall' d hd with h1 | h1
  · have hba : b = a := h1.2 b hdab.2.1
    subst hba
    rcases hall d' hd' with h2 | h2
    · exact (h2.2 b' hdab'.2.1).symm
    · rcases h2.2.2 b' hdab'.2.1 with h3 | h3 <;> exact h3.symm
  · rcases h1.2.2 b hdab.2.1 with h2 | h2
    · subst h2
      rcases hall d' hd' with h3 | h3
      · exact (h3.2 b' hdab'.2.1).symm
      · rcases h3.2.2 b' hdab'.2.1 with h4 | h4 <;> exact h4.symm
    · exact h2

theorem pr_iff_of_spec {r : V} {P : V → V → Prop}
    (hr : ∀ q, q ∈ r ↔ ∃ a b, IsOp q a b ∧ P a b) (hex : ∀ a b, P a b → ∃ q, IsOp q a b)
    (a b : V) : Pr r a b ↔ P a b := by
  constructor
  · rintro ⟨q, hq, hop⟩
    obtain ⟨a', b', hop', hP⟩ := (hr q).mp hq
    obtain ⟨rfl, rfl⟩ := op_inj hop hop'
    exact hP
  · intro hP
    obtain ⟨q, hq⟩ := hex a b hP
    exact ⟨q, (hr q).mpr ⟨a, b, hq, hP⟩, hq⟩

end pairs

end MH

/-! ### The theory -/

namespace Axiom

/-- The collapse axiom. -/
def collapse : SetTheorySentence := MH.hcF.φ

end Axiom

/-- The theory containing only the collapse axiom. -/
def CollapseAxiom : SetTheory := {Axiom.collapse}

/-- `𝗠` with the collapse axiom. -/
abbrev MathiasMH : SetTheory := 𝗠 ∪ CollapseAxiom

/-- `𝗠` with the collapse axiom. -/
notation "𝗠𝗛" => MathiasMH

instance : 𝗠 ⪯ 𝗠𝗛 := Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h

instance : 𝗘𝗤 _ ⪯ 𝗠𝗛 :=
  let : 𝗘𝗤 _ ⪯ 𝗠 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

section model

variable {V : Type} [SetStructure V] [Nonempty V]

instance [V↓[ℒₛₑₜ] ⊧* 𝗠𝗛] : V↓[ℒₛₑₜ] ⊧* 𝗠 := models_of_subtheory (U := 𝗠𝗛) inferInstance

/-- **In a model of `𝗠𝗛` the collapse axiom holds.** -/
theorem MH.hc_of_models [h : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛] : MH.HC V := by
  have h1 := Theory.models V 𝗠𝗛 (show Axiom.collapse ∈ 𝗠𝗛 from Or.inr rfl)
  exact (MH.hcF.eval V ![]).mp (by simpa [models_iff, Axiom.collapse] using h1)

/-- **A model of `𝗠` in which the collapse axiom holds is a model of `𝗠𝗛`.** -/
theorem MH.models_of_hc [h : V↓[ℒₛₑₜ] ⊧* 𝗠] (hc : MH.HC V) : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp h φ hφ
  · have e : φ = Axiom.collapse := hφ
    rw [e]
    have := (MH.hcF.eval V ![]).mpr hc
    simpa [models_iff, Axiom.collapse] using this

end model

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.hc_of_models
#print axioms FFL.FirstOrder.SetTheory.MH.models_of_hc
