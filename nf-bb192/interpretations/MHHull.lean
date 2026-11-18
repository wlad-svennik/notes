import MHExist

set_option autoImplicit false

/-!
# Hulls and the collapse axiom

Inside a model `V` of `𝗠`.

* `hcat_image`: if `T` is a set as in the collapse axiom for `U`, and `N` is the image of `U`
  under a function, then `T` is a set as in the collapse axiom for `N`.
* `hull_exists`: for a partial function `gen` on a set `G₀` and a partial function `g` of four
  arguments (both given as sets of pairs), there is a set `N` that contains the values of `gen`
  and is closed under `g`, and `N` is the image under a function of the fixed set `HCd G₀` of
  tree codes with labels in `ω ∪ G₀`. The codes are evaluated by recursion on their depth.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section image

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- **The collapse axiom passes to images.** -/
theorem hcat_image {T U N Vl : V} (hT : HCat T U)
    (hN : ∀ x, x ∈ N ↔ ∃ c, c ∈ U ∧ Pr Vl c x)
    (hfun : ∀ c x x', Pr Vl c x → Pr Vl c x' → x = x') : HCat T N := by
  refine ⟨hT.1, fun r hwf => ?_⟩
  let r' : V := relB (k := 3) (BDef.bex 2 (BDef.bex 3 ((prB.comp ![5, 3, 1]).and
    ((prB.comp ![5, 2, 0]).and (prB.comp ![6, 0, 1]))))) U U ![N, Vl, r]
  have hr' : ∀ c' c, Pr r' c' c ↔ c' ∈ U ∧ c ∈ U ∧ ∃ x, x ∈ N ∧ ∃ x', x' ∈ N ∧
      (Pr Vl c x ∧ (Pr Vl c' x' ∧ Pr r x' x)) := fun c' c => pr_relB _ _ _ _ c' c
  have hwf' : WFon r' U := by
    rintro X' ⟨c₀, hc₀, -⟩ -
    let X : V := sepB (k := 2) (BDef.bex 1 (prB.comp ![3, 0, 1])) N ![X', Vl]
    have hX : ∀ x, x ∈ X ↔ x ∈ N ∧ ∃ c, c ∈ X' ∧ Pr Vl c x := fun x => mem_sepB _ _ _ x
    by_cases hne : ∃ x, x ∈ X
    · obtain ⟨x₀, hx₀⟩ := hne
      obtain ⟨m, hm, hmin⟩ := hwf X ⟨x₀, hx₀, not_false⟩ (fun x hx => ((hX x).mp hx).1)
      obtain ⟨-, c, hcX', hcm⟩ := (hX m).mp hm
      refine ⟨c, hcX', fun c' hc' hrc => ?_⟩
      obtain ⟨-, -, x, -, x', hx'N, h1, h2, h3⟩ := (hr' c' c).mp hrc
      have e : x = m := hfun c x m h1 hcm
      rw [e] at h3
      exact hmin x' ((hX x').mpr ⟨hx'N, c', hc', h2⟩) h3
    · refine ⟨c₀, hc₀, fun c' _ hrc => hne ?_⟩
      obtain ⟨-, -, x, hxN, x', -, h1, -, -⟩ := (hr' c' c₀).mp hrc
      exact ⟨x, (hX x).mpr ⟨hxN, c₀, hc₀, h1⟩⟩
  obtain ⟨F', hF'⟩ := hT.2 r' hwf'
  let P : V := relB (k := 3) (BDef.bex 2 ((prB.comp ![4, 0, 1]).and (prB.comp ![5, 0, 2])))
    N T ![U, Vl, F']
  have hP : ∀ x v, Pr P x v ↔ x ∈ N ∧ v ∈ T ∧ ∃ c, c ∈ U ∧ (Pr Vl c x ∧ Pr F' c v) :=
    fun x v => pr_relB _ _ _ _ x v
  have hpred : ∀ c c₂ b c', Pr Vl c b → Pr Vl c₂ b → c₂ ∈ U → Pr r' c' c → Pr r' c' c₂ := by
    intro c c₂ b c' h1 h2 hc₂ hrc
    obtain ⟨hc', -, x, hxN, x', hx'N, g1, g2, g3⟩ := (hr' c' c).mp hrc
    have e : x = b := hfun c x b g1 h1
    rw [e] at g3 hxN
    exact (hr' c' c₂).mpr ⟨hc', hc₂, b, hxN, x', hx'N, h2, g2, g3⟩
  refine ⟨P, fun b hb => ?_⟩
  obtain ⟨c, hc, hcb⟩ := (hN b).mp hb
  obtain ⟨v, hvT, hcv, hvu, hvm⟩ := hF' c hc
  refine ⟨v, hvT, (hP b v).mpr ⟨hb, hvT, c, hc, hcb, hcv⟩, fun v' hv' => ?_, fun y => ?_⟩
  · obtain ⟨-, -, c₂, hc₂, h1, h2⟩ := (hP b v').mp hv'
    obtain ⟨v₂, -, -, hv₂u, hv₂m⟩ := hF' c₂ hc₂
    rw [hv₂u v' h2]
    refine mem_ext fun y => ?_
    rw [hv₂m, hvm]
    exact ⟨fun ⟨a, ha, h3, h4⟩ => ⟨a, ha, hpred c₂ c b a h1 hcb hc h3, h4⟩,
      fun ⟨a, ha, h3, h4⟩ => ⟨a, ha, hpred c c₂ b a hcb h1 hc₂ h3, h4⟩⟩
  · rw [hvm]
    constructor
    · rintro ⟨c', hc', hrc, hFy⟩
      obtain ⟨-, -, x, -, x', hx'N, g1, g2, g3⟩ := (hr' c' c).mp hrc
      have e : x = b := hfun c x b g1 hcb
      rw [e] at g3
      have hyT : y ∈ T := hT.1 v hvT y ((hvm y).mpr ⟨c', hc', hrc, hFy⟩)
      exact ⟨x', hx'N, g3, (hP x' y).mpr ⟨hx'N, hyT, c', hc', g2, hFy⟩⟩
    · rintro ⟨a, haN, hrab, hPa⟩
      obtain ⟨-, -, c', hc', h1, h2⟩ := (hP a y).mp hPa
      exact ⟨c', hc', (hr' c' c).mpr ⟨hc', hc, b, hb, a, haN, hcb, h1, hrab⟩, h2⟩

end image

section defs

variable {V : Type} [SetStructure V]

/-- `e` is the pair of the four-tuple `(y₀, y₁, y₂, y₃)` and `x`. -/
def IsQ5 (e y₀ y₁ y₂ y₃ x : V) : Prop :=
  ∃ u, u ∈ e ∧ ∃ q, q ∈ u ∧ ∃ u₁, u₁ ∈ q ∧ ∃ r₁, r₁ ∈ u₁ ∧ ∃ u₂, u₂ ∈ r₁ ∧ ∃ r₂, r₂ ∈ u₂ ∧
    (IsOp e q x ∧ (IsOp q y₀ r₁ ∧ (IsOp r₁ y₁ r₂ ∧ IsOp r₂ y₂ y₃)))

/-- The relation `g` holds between the four-tuple `(y₀, y₁, y₂, y₃)` and `x`. -/
def Ap4 (g y₀ y₁ y₂ y₃ x : V) : Prop := ∃ e, e ∈ g ∧ IsQ5 e y₀ y₁ y₂ y₃ x

/-- `a` is the only label of the root of `c`. -/
def RootIs (c a z0 Lb : V) : Prop := Pr c z0 a ∧ ∀ a', a' ∈ Lb → Pr c z0 a' → a' = a

/-- The value of a code of depth zero: the value of `gen` at the label of its first subtree. -/
def ValLeaf (c x gen z0 Cd K0 G₀ Lb : V) : Prop :=
  ∃ c₀, c₀ ∈ Cd ∧ (Pr K0 c c₀ ∧ ∃ a, a ∈ G₀ ∧ (RootIs c₀ a z0 Lb ∧ Pr gen a x))

/-- The value of a code of positive depth: `g` applied to the earlier values of its subtrees. -/
def ValNode (h β c x g Cd K0 K1 K2 K3 Ax : V) : Prop :=
  ∃ y₀, y₀ ∈ Ax ∧ ∃ y₁, y₁ ∈ Ax ∧ ∃ y₂, y₂ ∈ Ax ∧ ∃ y₃, y₃ ∈ Ax ∧
    (Kids h β c y₀ y₁ y₂ y₃ Cd K0 K1 K2 K3 ∧ Ap4 g y₀ y₁ y₂ y₃ x)

/-- `x` is the value of the code `c` of depth `β`. -/
def ValN (h β c x gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb : V) : Prop :=
  RkC c β z0 ∧ (((∀ w, w ∈ β → False) ∧ ValLeaf c x gen z0 Cd K0 G₀ Lb) ∨
    ((∃ w, w ∈ β ∧ ¬False) ∧ ValNode h β c x g Cd K0 K1 K2 K3 Ax))

/-- The clause of the evaluation: `E` is the set of the pairs of a code of depth `β` and its
value. -/
def GEvN (β h E gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb : V) : Prop :=
  (∀ e, e ∈ E → ∃ c, c ∈ Cd ∧ ∃ x, x ∈ Ax ∧
    (IsOp e c x ∧ ValN h β c x gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb)) ∧
  (∀ c, c ∈ Cd → ∀ x, x ∈ Ax → ValN h β c x gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb → Pr E c x)

end defs

def isQ5B : BDef (k := 6) (fun V _ v ↦ IsQ5 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0
    ((isOpB.comp ![6, 4, 11]).and ((isOpB.comp ![4, 7, 2]).and ((isOpB.comp ![2, 8, 0]).and
      (isOpB.comp ![0, 9, 10])))))))))).congr fun _ _ _ => Iff.rfl

def ap4B : BDef (k := 6) (fun V _ v ↦ Ap4 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 0 (isQ5B.comp ![0, 2, 3, 4, 5, 6])).congr fun _ _ _ => Iff.rfl

def rootIsB : BDef (k := 4) (fun V _ v ↦ RootIs (v 0) (v 1) (v 2) (v 3)) :=
  ((prB.comp ![0, 2, 1]).and (BDef.ball 3 ((prB.comp ![1, 3, 0]).imp (BDef.eq 0 2)))).congr
    fun _ _ _ => Iff.rfl

def valLeafB : BDef (k := 8) (fun V _ v ↦ ValLeaf (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
    (v 7)) :=
  (BDef.bex 4 ((prB.comp ![6, 1, 0]).and (BDef.bex 7 ((rootIsB.comp ![1, 0, 5, 9]).and
    (prB.comp ![4, 0, 3]))))).congr fun _ _ _ => Iff.rfl

def valNodeB : BDef (k := 11) (fun V _ v ↦ ValNode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
    (v 7) (v 8) (v 9) (v 10)) :=
  (BDef.bex 10 (BDef.bex 11 (BDef.bex 12 (BDef.bex 13
    ((kidsB.comp ![4, 5, 6, 3, 2, 1, 0, 9, 10, 11, 12, 13]).and
      (ap4B.comp ![8, 3, 2, 1, 0, 7])))))).congr fun _ _ _ => Iff.rfl

def valNB : BDef (k := 15) (fun V _ v ↦ ValN (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14)) :=
  ((rkCB.comp ![2, 1, 6]).and
    (((BDef.ball 1 BDef.fls).and (valLeafB.comp ![2, 3, 4, 6, 7, 8, 13, 14])).or
    ((BDef.bex 1 BDef.fls.not).and
      (valNodeB.comp ![0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12])))).congr fun _ _ _ => Iff.rfl

def gEvNB : BDef (k := 14) (fun V _ v ↦ GEvN (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10) (v 11) (v 12) (v 13)) :=
  ((BDef.ball 2 (BDef.bex 7 (BDef.bex 13 ((isOpB.comp ![2, 1, 0]).and
    (valNB.comp ![4, 3, 1, 0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]))))).and
  (BDef.ball 6 (BDef.ball 12 ((valNB.comp ![3, 2, 1, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]).imp
    (prB.comp ![4, 1, 0]))))).congr fun _ _ _ => Iff.rfl

/-- The clause of the evaluation as a relation of fourteen arguments. -/
def GEvNR : MRel 14 := fun V _ v ↦ GEvN (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10) (v 11) (v 12) (v 13)

section hull

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem isQ5_iff {e y₀ y₁ y₂ y₃ x : V} :
    IsQ5 e y₀ y₁ y₂ y₃ x ↔ e = kp (kp y₀ (kp y₁ (kp y₂ y₃))) x := by
  constructor
  · rintro ⟨u, -, q, -, u₁, -, r₁, -, u₂, -, r₂, -, h1, h2, h3, h4⟩
    have e4 := isOp_iff.mp h4
    subst e4
    have e3 := isOp_iff.mp h3
    subst e3
    have e2 := isOp_iff.mp h2
    subst e2
    exact isOp_iff.mp h1
  · intro h
    obtain ⟨u, hu, hqu⟩ := pr_fst_mem (isOp_kp (kp y₀ (kp y₁ (kp y₂ y₃))) x)
    obtain ⟨u₁, hu₁, hr₁⟩ := pr_snd_mem (isOp_kp y₀ (kp y₁ (kp y₂ y₃)))
    obtain ⟨u₂, hu₂, hr₂⟩ := pr_snd_mem (isOp_kp y₁ (kp y₂ y₃))
    rw [h]
    exact ⟨u, hu, _, hqu, u₁, hu₁, _, hr₁, u₂, hu₂, _, hr₂, isOp_kp _ _, isOp_kp _ _,
      isOp_kp _ _, isOp_kp _ _⟩

theorem valN_congr {h h' β : V} (hag : ∀ β', β' ∈ β → ∀ E, Pr h β' E ↔ Pr h' β' E)
    (c x gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb : V) :
    ValN h β c x gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb ↔
      ValN h' β c x gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb := by
  have e := valH_congr hag
  simp only [ValN, ValNode, Kids, e]

theorem gEvN_loc (γ h h' E gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb : V)
    (hag : ∀ β', β' ∈ γ → ∀ E, Pr h β' E ↔ Pr h' β' E)
    (hG : GEvN γ h E gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb) :
    GEvN γ h' E gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb := by
  have e := valN_congr hag
  simp only [GEvN, e] at hG ⊢
  exact hG

theorem gEvN_uniq (γ h E E' gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb : V)
    (hG : GEvN γ h E gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb)
    (hG' : GEvN γ h E' gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb) : E = E' := by
  have key : ∀ E E' : V, GEvN γ h E gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb →
      GEvN γ h E' gen g z0 Cd K0 K1 K2 K3 Ax G₀ Lb → ∀ e, e ∈ E → e ∈ E' := by
    intro E E' hG hG' e he
    obtain ⟨c, hc, x, hx, hop, hv⟩ := hG.1 e he
    rw [isOp_iff.mp hop]
    exact pr_iff.mp (hG'.2 c hc x hx hv)
  exact mem_ext fun e => ⟨key E E' hG hG' e, key E' E hG' hG e⟩

theorem om_max2 {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) :
    ∃ m, m ∈ (om : V) ∧ a ∈ m ∧ b ∈ m := by
  rcases ord_tri (ord_mem ord_om ha) (ord_mem ord_om hb) with h | h | h
  · exact ⟨sc b, sc_mem_om hb, mem_sc.mpr (Or.inr h), self_mem_sc b⟩
  · exact ⟨sc b, sc_mem_om hb, mem_sc.mpr (Or.inl h), self_mem_sc b⟩
  · exact ⟨sc a, sc_mem_om ha, self_mem_sc a, mem_sc.mpr (Or.inr h)⟩

/-- The set of the codes for a hull with generators labelled by `G₀`. -/
noncomputable def HCd (G₀ : V) : V := CdS ((om : V) ∪ G₀)

/-- **Hulls exist, and are images of the set of the codes.** -/
theorem hull_exists {W G₀ gen g : V}
    (hgen : ∀ a x x', Pr gen a x → Pr gen a x' → x = x')
    (hg : ∀ y₀ y₁ y₂ y₃ x x', Ap4 g y₀ y₁ y₂ y₃ x → Ap4 g y₀ y₁ y₂ y₃ x' → x = x') :
    ∃ N Vl : V, (∀ x, x ∈ N → x ∈ W) ∧
      (∀ a x, a ∈ G₀ → x ∈ W → Pr gen a x → x ∈ N) ∧
      (∀ y₀ y₁ y₂ y₃ x, y₀ ∈ N → y₁ ∈ N → y₂ ∈ N → y₃ ∈ N → x ∈ W →
        Ap4 g y₀ y₁ y₂ y₃ x → x ∈ N) ∧
      (∀ x, x ∈ N ↔ ∃ c, c ∈ HCd G₀ ∧ Pr Vl c x) ∧
      (∀ c x x', Pr Vl c x → Pr Vl c x' → x = x') := by
  let Lb : V := (om : V) ∪ G₀
  let Cd : V := CdS Lb
  let K : Fin 4 → V := fun j => kidS Lb j
  let p : Fin 11 → V := ![gen, g, ∅, Cd, K 0, K 1, K 2, K 3, W, G₀, Lb]
  have hLb1 : ∀ z, z ∈ (om : V) → z ∈ Lb := fun z h => mem_union_iff.mpr (Or.inl h)
  have hLb2 : ∀ z, z ∈ G₀ → z ∈ Lb := fun z h => mem_union_iff.mpr (Or.inr h)
  have hloc : ∀ γ h h' E : V, Ord γ → (∀ γ', γ' ∈ γ → ∀ y', Pr h γ' y' ↔ Pr h' γ' y') →
      GEvNR V (γ :> h :> E :> p) → GEvNR V (γ :> h' :> E :> p) := fun γ h h' E _ hag hG =>
    gEvN_loc γ h h' E gen g ∅ Cd (K 0) (K 1) (K 2) (K 3) W G₀ Lb hag hG
  have huniq : ∀ γ h E E' : V, GEvNR V (γ :> h :> E :> p) → GEvNR V (γ :> h :> E' :> p) →
      E = E' := fun γ h E E' hG hG' =>
    gEvN_uniq γ h E E' gen g ∅ Cd (K 0) (K 1) (K 2) (K 3) W G₀ Lb hG hG'
  obtain ⟨H, hH⟩ := ord_rec (k := 11) (G := GEvNR) gEvNB hloc huniq (om : V) (℘ (prodS Cd W))
    ord_om (fun β₁ _ h _ _ => by
      let E : V := relB (k := 13)
        (valNB.comp ![2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]) Cd W
        ![h, β₁, gen, g, ∅, Cd, K 0, K 1, K 2, K 3, W, G₀, Lb]
      have hE : ∀ c x, Pr E c x ↔ c ∈ Cd ∧ x ∈ W ∧
          ValN h β₁ c x gen g ∅ Cd (K 0) (K 1) (K 2) (K 3) W G₀ Lb :=
        fun c x => pr_relB _ _ _ _ c x
      have hEs : ∀ e, e ∈ E → e ∈ prodS Cd W := fun e he => relB_sub _ _ _ _ he
      refine ⟨E, mem_power_iff.mpr hEs, fun e he => ?_,
        fun c hc x hx hv => (hE c x).mpr ⟨hc, hx, hv⟩⟩
      have he' : e ∈ E := he
      obtain ⟨c, hc, x, hx, rfl⟩ := mem_prodS.mp (hEs e he')
      exact ⟨c, hc, x, hx, isOp_kp c x, ((hE c x).mp (pr_iff.mpr he')).2.2⟩)
  have hHfun : ∀ {n E E' : V}, Pr H n E → Pr H n E' → E = E' := fun h1 h2 => att_fun hH h1 h2
  have hEiff : ∀ n E, Pr H n E → ∀ c x, Pr E c x ↔ c ∈ Cd ∧ x ∈ W ∧
      ValN H n c x gen g ∅ Cd (K 0) (K 1) (K 2) (K 3) W G₀ Lb := by
    intro n E hE c x
    have hG : GEvN n H E gen g ∅ Cd (K 0) (K 1) (K 2) (K 3) W G₀ Lb := att_G hH hE
    constructor
    · rintro ⟨e, he, hop⟩
      obtain ⟨c', hc', x', hx', hop', hv⟩ := hG.1 e he
      obtain ⟨rfl, rfl⟩ := op_inj hop hop'
      exact ⟨hc', hx', hv⟩
    · rintro ⟨hc, hx, hv⟩
      exact hG.2 c hc x hx hv
  have kids_iff : ∀ n c (y : Fin 4 → V), c ∈ Cd →
      (Kids H n c (y 0) (y 1) (y 2) (y 3) Cd (K 0) (K 1) (K 2) (K 3) ↔
        ∀ j : Fin 4, ValH H n (chC Tg4 Lb (nm j) c) (y j)) := by
    intro n c y hc
    constructor
    · rintro ⟨c₀, -, c₁, -, c₂, -, c₃, -, ⟨k0, v0⟩, ⟨k1, v1⟩, ⟨k2, v2⟩, ⟨k3, v3⟩⟩ j
      have e0 := (pr_kidS.mp k0).2
      have e1 := (pr_kidS.mp k1).2
      have e2 := (pr_kidS.mp k2).2
      have e3 := (pr_kidS.mp k3).2
      subst e0 e1 e2 e3
      match j with
      | 0 => exact v0
      | 1 => exact v1
      | 2 => exact v2
      | 3 => exact v3
    · intro h
      exact ⟨_, chC_mem, _, chC_mem, _, chC_mem, _, chC_mem,
        ⟨pr_kidS.mpr ⟨hc, rfl⟩, h 0⟩, ⟨pr_kidS.mpr ⟨hc, rfl⟩, h 1⟩,
        ⟨pr_kidS.mpr ⟨hc, rfl⟩, h 2⟩, ⟨pr_kidS.mpr ⟨hc, rfl⟩, h 3⟩⟩
  have hOn : ∀ n, n ∈ (om : V) → Ord n := fun n hn => ord_mem ord_om hn
  -- the values are unique
  have hfunS : ∀ n, n ∈ (om : V) → ∀ E, Pr H n E → FunS E := by
    by_contra hcon
    let Z : V := sepB (k := 1) (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and
      (funSB.comp ![0]).not)))) (om : V) ![H]
    have hZ : ∀ n, n ∈ Z ↔ n ∈ (om : V) ∧ ∃ q, q ∈ H ∧ ∃ u, u ∈ q ∧ ∃ E, E ∈ u ∧
        (IsOp q n E ∧ ¬FunS E) := fun n => mem_sepB _ _ _ n
    have hne : ∃ n, n ∈ Z := by
      by_contra h
      refine hcon fun n hn E hE => ?_
      by_contra hnF
      obtain ⟨q, hq, hop⟩ := hE
      obtain ⟨u, hu, hEu⟩ := pr_snd_mem hop
      exact h ⟨n, (hZ n).mpr ⟨hn, q, hq, u, hu, E, hEu, hop, hnF⟩⟩
    obtain ⟨n, hnZ, hmin⟩ := ord_least Z (fun z hz => hOn z ((hZ z).mp hz).1) hne
    obtain ⟨hn, q, hq, u, -, E, -, hop, hnE⟩ := (hZ n).mp hnZ
    have hE : Pr H n E := ⟨q, hq, hop⟩
    have hlow : ∀ c' y y', ValH H n c' y → ValH H n c' y' → y = y' := by
      intro c' y y' hy hy'
      obtain ⟨n₁, hn₁, E₁, hE₁, hp₁⟩ := valH_iff.mp hy
      obtain ⟨n₂, hn₂, E₂, hE₂, hp₂⟩ := valH_iff.mp hy'
      have hn₁o := om_tr n hn n₁ hn₁
      have hn₂o := om_tr n hn n₂ hn₂
      have hr₁ := ((hEiff n₁ E₁ hE₁ c' y).mp hp₁).2.2.1
      have hr₂ := ((hEiff n₂ E₂ hE₂ c' y').mp hp₂).2.2.1
      have e : n₁ = n₂ := rkC_unique (hOn n₁ hn₁o) (hOn n₂ hn₂o) hr₁ hr₂
      subst e
      have e : E₁ = E₂ := hHfun hE₁ hE₂
      subst e
      have hF₁ : FunS E₁ := by
        by_contra hnF
        obtain ⟨q₁, hq₁, hop₁⟩ := hE₁
        obtain ⟨u₁, hu₁, hEu₁⟩ := pr_snd_mem hop₁
        rcases hmin n₁ ((hZ n₁).mpr ⟨hn₁o, q₁, hq₁, u₁, hu₁, E₁, hEu₁, hop₁, hnF⟩) with e | e
        · rw [e] at hn₁
          exact mem_irrefl n₁ hn₁
        · exact mem_asymm e hn₁
      exact funS_apply hF₁ hp₁ hp₂
    refine hnE fun e he e' he' u _ c _ u₁ _ x _ u₂ _ x' _ hop hop' => ?_
    obtain ⟨hc, -, -, hv⟩ := (hEiff n E hE c x).mp ⟨e, he, hop⟩
    obtain ⟨-, -, -, hv'⟩ := (hEiff n E hE c x').mp ⟨e', he', hop'⟩
    rcases hv with ⟨hz, c₀, -, hk, a, -, hroot, hga⟩ | ⟨hnz, y₀, -, y₁, -, y₂, -, y₃, -, hk, hap⟩
    · rcases hv' with ⟨-, c₀', -, hk', a', ha', hroot', hga'⟩ | ⟨⟨w, hw, -⟩, -⟩
      · have e1 : c₀ = c₀' := (pr_kidS.mp hk).2.trans (pr_kidS.mp hk').2.symm
        rw [← e1] at hroot'
        have e2 : a' = a := hroot.2 a' (hLb2 a' ha') hroot'.1
        rw [e2] at hga'
        exact hgen a x x' hga hga'
      · exact (hz w hw).elim
    · rcases hv' with ⟨hz, -⟩ | ⟨-, z₀, -, z₁, -, z₂, -, z₃, -, hk', hap'⟩
      · obtain ⟨w, hw, -⟩ := hnz
        exact (hz w hw).elim
      · have h1 := (kids_iff n c ![y₀, y₁, y₂, y₃] hc).mp hk
        have h2 := (kids_iff n c ![z₀, z₁, z₂, z₃] hc).mp hk'
        have e0 : y₀ = z₀ := hlow _ _ _ (h1 0) (h2 0)
        have e1 : y₁ = z₁ := hlow _ _ _ (h1 1) (h2 1)
        have e2 : y₂ = z₂ := hlow _ _ _ (h1 2) (h2 2)
        have e3 : y₃ = z₃ := hlow _ _ _ (h1 3) (h2 3)
        subst e0 e1 e2 e3
        exact hg _ _ _ _ x x' hap hap'
  let Vl : V := relB (k := 2) (valHB.comp ![2, 3, 0, 1]) Cd W ![H, (om : V)]
  have hVl : ∀ c x, Pr Vl c x ↔ c ∈ Cd ∧ x ∈ W ∧ ValH H (om : V) c x :=
    fun c x => pr_relB _ _ _ _ c x
  let N : V := sepB (k := 2) (BDef.bex 1 (prB.comp ![3, 0, 1])) W ![Cd, Vl]
  have hN : ∀ x, x ∈ N ↔ x ∈ W ∧ ∃ c, c ∈ Cd ∧ Pr Vl c x := fun x => mem_sepB _ _ _ x
  have hstage : ∀ n, n ∈ (om : V) → ∃ E, Pr H n E := fun n hn =>
    let ⟨E, hE, _⟩ := att_total hH (mem_sc.mpr (Or.inr hn)); ⟨E, hE⟩
  have hput : ∀ n c x, n ∈ (om : V) → c ∈ Cd → x ∈ W →
      ValN H n c x gen g ∅ Cd (K 0) (K 1) (K 2) (K 3) W G₀ Lb → x ∈ N := by
    intro n c x hn hc hx hv
    obtain ⟨E, hE⟩ := hstage n hn
    exact (hN x).mpr ⟨hx, c, hc, (hVl c x).mpr ⟨hc, hx,
      valH_iff.mpr ⟨n, hn, E, hE, (hEiff n E hE c x).mpr ⟨hc, hx, hv⟩⟩⟩⟩
  have hemp : (∅ : V) ∈ Cd := mem_power_iff.mpr fun z hz => absurd hz (by simp)
  refine ⟨N, Vl, fun x hx => ((hN x).mp hx).1, fun a x ha hx hpr => ?_,
    fun y₀ y₁ y₂ y₃ x h₀ h₁ h₂ h₃ hx hap => ?_,
    fun x => ⟨fun hx => ((hN x).mp hx).2, fun ⟨c, hc, hv⟩ => (hN x).mpr ⟨((hVl c x).mp hv).2.1,
      c, hc, hv⟩⟩, fun c x x' h h' => ?_⟩
  · -- generators
    have hc₀ : mk4 Lb a (fun _ ↦ (∅ : V)) ∈ Cd := mk4_mem (hLb2 a ha)
    have hcc : ∀ j : Fin 4, (![mk4 Lb a (fun _ ↦ (∅ : V)), ∅, ∅, ∅] : Fin 4 → V) j ∈ Cd := by
      intro j
      match j with
      | 0 => exact hc₀
      | 1 => exact hemp
      | 2 => exact hemp
      | 3 => exact hemp
    have hc : mk4 Lb ∅ ![mk4 Lb a (fun _ ↦ (∅ : V)), ∅, ∅, ∅] ∈ Cd :=
      mk4_mem (hLb1 _ empty_mem_om)
    refine hput ∅ _ x empty_mem_om hc hx ⟨⟨pr_mk4_root.mpr rfl, fun γ hγ => absurd hγ (by simp)⟩,
      Or.inl ⟨fun w hw => absurd hw (by simp), mk4 Lb a (fun _ ↦ (∅ : V)), hc₀,
        pr_kidS.mpr ⟨hc, (chC_mk4 hcc 0).symm⟩, a, ha,
        ⟨pr_mk4_root.mpr rfl, fun a' _ h => pr_mk4_root.mp h⟩, hpr⟩⟩
  · -- closure under `g`
    obtain ⟨hy₀, c₀, hc₀, hv₀⟩ := (hN y₀).mp h₀
    obtain ⟨hy₁, c₁, hc₁, hv₁⟩ := (hN y₁).mp h₁
    obtain ⟨hy₂, c₂, hc₂, hv₂⟩ := (hN y₂).mp h₂
    obtain ⟨hy₃, c₃, hc₃, hv₃⟩ := (hN y₃).mp h₃
    obtain ⟨n₀, hn₀, E₀, hE₀, hp₀⟩ := valH_iff.mp ((hVl c₀ y₀).mp hv₀).2.2
    obtain ⟨n₁, hn₁, E₁, hE₁, hp₁⟩ := valH_iff.mp ((hVl c₁ y₁).mp hv₁).2.2
    obtain ⟨n₂, hn₂, E₂, hE₂, hp₂⟩ := valH_iff.mp ((hVl c₂ y₂).mp hv₂).2.2
    obtain ⟨n₃, hn₃, E₃, hE₃, hp₃⟩ := valH_iff.mp ((hVl c₃ y₃).mp hv₃).2.2
    obtain ⟨m₁, hm₁, a₀, a₁⟩ := om_max2 hn₀ hn₁
    obtain ⟨m₂, hm₂, a₂, a₃⟩ := om_max2 hn₂ hn₃
    obtain ⟨n, hn, b₁, b₂⟩ := om_max2 hm₁ hm₂
    have hnO := hOn n hn
    have hcc : ∀ j : Fin 4, (![c₀, c₁, c₂, c₃] : Fin 4 → V) j ∈ Cd := by
      intro j
      match j with
      | 0 => exact hc₀
      | 1 => exact hc₁
      | 2 => exact hc₂
      | 3 => exact hc₃
    have hc : mk4 Lb n ![c₀, c₁, c₂, c₃] ∈ Cd := mk4_mem (hLb1 n hn)
    refine hput n _ x hn hc hx ⟨⟨pr_mk4_root.mpr rfl, fun γ hγ hp => ?_⟩,
      Or.inr ⟨⟨m₁, b₁, not_false⟩, y₀, hy₀, y₁, hy₁, y₂, hy₂, y₃, hy₃, ?_, hap⟩⟩
    · rw [pr_mk4_root.mp hp] at hγ
      exact mem_irrefl _ hγ
    · refine (kids_iff n _ ![y₀, y₁, y₂, y₃] hc).mpr fun j => ?_
      rw [chC_mk4 hcc j]
      match j with
      | 0 => exact valH_iff.mpr ⟨n₀, hnO.1 m₁ b₁ n₀ a₀, E₀, hE₀, hp₀⟩
      | 1 => exact valH_iff.mpr ⟨n₁, hnO.1 m₁ b₁ n₁ a₁, E₁, hE₁, hp₁⟩
      | 2 => exact valH_iff.mpr ⟨n₂, hnO.1 m₂ b₂ n₂ a₂, E₂, hE₂, hp₂⟩
      | 3 => exact valH_iff.mpr ⟨n₃, hnO.1 m₂ b₂ n₃ a₃, E₃, hE₃, hp₃⟩
  · -- the value of a code is unique
    obtain ⟨n₁, hn₁, E₁, hE₁, hp₁⟩ := valH_iff.mp ((hVl c x).mp h).2.2
    obtain ⟨n₂, hn₂, E₂, hE₂, hp₂⟩ := valH_iff.mp ((hVl c x').mp h').2.2
    have hr₁ := ((hEiff n₁ E₁ hE₁ c x).mp hp₁).2.2.1
    have hr₂ := ((hEiff n₂ E₂ hE₂ c x').mp hp₂).2.2.1
    have e : n₁ = n₂ := rkC_unique (hOn n₁ hn₁) (hOn n₂ hn₂) hr₁ hr₂
    subst e
    have e : E₁ = E₂ := hHfun hE₁ hE₂
    subst e
    exact funS_apply (hfunS n₁ hn₁ E₁ hE₁) hp₁ hp₂

end hull

end MH

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.hull_exists
#print axioms FFL.FirstOrder.SetTheory.MH.hcat_image
