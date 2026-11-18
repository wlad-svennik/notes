import MHCodes

set_option autoImplicit false

/-!
# The levels exist along every ordinal

Inside a model `V` of `𝗠𝗛`.

Given the levels below a stage `β`, the next level `A` is a set of subsets of the earlier
levels. To continue the recursion one needs all the levels inside one set. Here the collapse
axiom is used: codes are evaluated by recursion on the label of their root (`GEv`), every member
of `A` is the value of a code (`coded`), and the relation "the value of `c'` is a member of the
value of `c`" on the set of the codes collapses onto `A`. So `A` is included in the transitive
set that the collapse axiom gives for the set of the codes (`next_sub`).

* `exists_hier`: for every ordinal `δ` there is a sequence of the levels up to `δ`.
* `Lev γ`, `LtS γ`: the level at `γ` and its order.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section defs

variable {V : Type} [SetStructure V]

/-- The code `c` has the value `y` at an earlier stage of `h`. -/
def ValH (h β c y : V) : Prop :=
  ∃ β', β' ∈ β ∧ ∃ q, q ∈ h ∧ ∃ u, u ∈ q ∧ ∃ E, E ∈ u ∧ (IsOp q β' E ∧ Pr E c y)

/-- The four subtrees of `c` have the earlier values `y₀, …, y₃`. -/
def Kids (h β c y₀ y₁ y₂ y₃ Cd K0 K1 K2 K3 : V) : Prop :=
  ∃ c₀, c₀ ∈ Cd ∧ ∃ c₁, c₁ ∈ Cd ∧ ∃ c₂, c₂ ∈ Cd ∧ ∃ c₃, c₃ ∈ Cd ∧
    ((Pr K0 c c₀ ∧ ValH h β c₀ y₀) ∧ ((Pr K1 c c₁ ∧ ValH h β c₁ y₁) ∧
      ((Pr K2 c c₂ ∧ ValH h β c₂ y₂) ∧ (Pr K3 c c₃ ∧ ValH h β c₃ y₃))))

/-- `x` is the value of `c` over the level `A`: the set defined from the values of the
subtrees if they all have values in `A`, and `A` otherwise. -/
def Val2 (h β c x A lt Cd K0 K1 K2 K3 : V) : Prop :=
  (∃ y₀, y₀ ∈ A ∧ ∃ y₁, y₁ ∈ A ∧ ∃ y₂, y₂ ∈ A ∧ ∃ y₃, y₃ ∈ A ∧
    (Kids h β c y₀ y₁ y₂ y₃ Cd K0 K1 K2 K3 ∧ IsD A lt y₀ y₁ y₂ y₃ x)) ∨
  (¬(∃ y₀, y₀ ∈ A ∧ ∃ y₁, y₁ ∈ A ∧ ∃ y₂, y₂ ∈ A ∧ ∃ y₃, y₃ ∈ A ∧
    Kids h β c y₀ y₁ y₂ y₃ Cd K0 K1 K2 K3) ∧ x = A)

/-- `x` is the value of the code `c`, whose root has least label `β`. -/
def Val1 (h β c x f z0 Cd K0 K1 K2 K3 : V) : Prop :=
  RkC c β z0 ∧ ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ d ∧
    ∃ lt, lt ∈ w' ∧ (IsOp q β d ∧ (IsOp d A lt ∧ Val2 h β c x A lt Cd K0 K1 K2 K3))

/-- The clause of the evaluation: `E` is the set of the pairs of a code with root label `β`
and its value. -/
def GEv (β h E f z0 Cd K0 K1 K2 K3 Ax : V) : Prop :=
  (∀ e, e ∈ E → ∃ c, c ∈ Cd ∧ ∃ x, x ∈ Ax ∧ (IsOp e c x ∧ Val1 h β c x f z0 Cd K0 K1 K2 K3)) ∧
  (∀ c, c ∈ Cd → ∀ x, x ∈ Ax → Val1 h β c x f z0 Cd K0 K1 K2 K3 → Pr E c x)

/-- Pairs with the same first component have the same second component. -/
def FunS (E : V) : Prop :=
  ∀ e, e ∈ E → ∀ e', e' ∈ E → ∀ u, u ∈ e → ∀ c, c ∈ u → ∀ u₁, u₁ ∈ e → ∀ x, x ∈ u₁ →
    ∀ u₂, u₂ ∈ e' → ∀ x', x' ∈ u₂ → IsOp e c x → IsOp e' c x' → x = x'

/-- `x` is the value of a code at a stage before `γ`. -/
def Coded (γ x H : V) : Prop :=
  ∃ β', β' ∈ γ ∧ ∃ q, q ∈ H ∧ ∃ u, u ∈ q ∧ ∃ E, E ∈ u ∧ (IsOp q β' E ∧
    ∃ e, e ∈ E ∧ ∃ u', u' ∈ e ∧ ∃ c, c ∈ u' ∧ IsOp e c x)

end defs

def valHB : BDef (k := 4) (fun V _ v ↦ ValH (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 1 (BDef.bex 1 (BDef.bex 0 (BDef.bex 0
    ((isOpB.comp ![2, 3, 0]).and (prB.comp ![0, 6, 7])))))).congr fun _ _ _ => Iff.rfl

def kidsB : BDef (k := 12) (fun V _ v ↦ Kids (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10) (v 11)) :=
  (BDef.bex 7 (BDef.bex 8 (BDef.bex 9 (BDef.bex 10
    (((prB.comp ![12, 6, 3]).and (valHB.comp ![4, 5, 3, 7])).and
    (((prB.comp ![13, 6, 2]).and (valHB.comp ![4, 5, 2, 8])).and
    (((prB.comp ![14, 6, 1]).and (valHB.comp ![4, 5, 1, 9])).and
    ((prB.comp ![15, 6, 0]).and (valHB.comp ![4, 5, 0, 10]))))))))).congr fun _ _ _ => Iff.rfl

def val2B : BDef (k := 11) (fun V _ v ↦ Val2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10)) :=
  ((BDef.bex 4 (BDef.bex 5 (BDef.bex 6 (BDef.bex 7
    ((kidsB.comp ![4, 5, 6, 3, 2, 1, 0, 10, 11, 12, 13, 14]).and
      (isDB.comp ![8, 9, 3, 2, 1, 0, 7])))))).or
  (((BDef.bex 4 (BDef.bex 5 (BDef.bex 6 (BDef.bex 7
    (kidsB.comp ![4, 5, 6, 3, 2, 1, 0, 10, 11, 12, 13, 14]))))).not).and (BDef.eq 3 4))).congr
    fun _ _ _ => Iff.rfl

def val1B : BDef (k := 11) (fun V _ v ↦ Val1 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10)) :=
  ((rkCB.comp ![2, 1, 5]).and (BDef.bex 4 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0
    (BDef.bex 2 (BDef.bex 0 ((isOpB.comp ![6, 8, 4]).and ((isOpB.comp ![4, 2, 0]).and
      (val2B.comp ![7, 8, 9, 10, 2, 0, 13, 14, 15, 16, 17]))))))))))).congr fun _ _ _ => Iff.rfl

def gEvB : BDef (k := 11) (fun V _ v ↦ GEv (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10)) :=
  ((BDef.ball 2 (BDef.bex 6 (BDef.bex 12 ((isOpB.comp ![2, 1, 0]).and
    (val1B.comp ![4, 3, 1, 0, 6, 7, 8, 9, 10, 11, 12]))))).and
  (BDef.ball 5 (BDef.ball 11 ((val1B.comp ![3, 2, 1, 0, 5, 6, 7, 8, 9, 10, 11]).imp
    (prB.comp ![4, 1, 0]))))).congr fun _ _ _ => Iff.rfl

def funSB : BDef (k := 1) (fun V _ v ↦ FunS (v 0)) :=
  (BDef.ball 0 (BDef.ball 1 (BDef.ball 1 (BDef.ball 0 (BDef.ball 3 (BDef.ball 0 (BDef.ball 4
    (BDef.ball 0 ((isOpB.comp ![7, 4, 2]).imp ((isOpB.comp ![6, 4, 0]).imp
      (BDef.eq 2 0))))))))))).congr fun _ _ _ => Iff.rfl

def codedB : BDef (k := 3) (fun V _ v ↦ Coded (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (BDef.bex 3 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and
    (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (isOpB.comp ![2, 0, 8]))))))))).congr
    fun _ _ _ => Iff.rfl

/-- The clause of the evaluation as a relation of eleven arguments. -/
def GEvR : MRel 11 := fun V _ v ↦ GEv (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    (v 8) (v 9) (v 10)

section bridge

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem valH_iff {h β c y : V} : ValH h β c y ↔ ∃ β', β' ∈ β ∧ ∃ E, Pr h β' E ∧ Pr E c y := by
  constructor
  · rintro ⟨β', hβ', q, hq, u, -, E, -, hop, hpr⟩
    exact ⟨β', hβ', E, ⟨q, hq, hop⟩, hpr⟩
  · rintro ⟨β', hβ', E, ⟨q, hq, hop⟩, hpr⟩
    obtain ⟨u, hu, hEu⟩ := pr_snd_mem hop
    exact ⟨β', hβ', q, hq, u, hu, E, hEu, hop, hpr⟩

theorem valH_congr {h h' β : V} (hag : ∀ β', β' ∈ β → ∀ E, Pr h β' E ↔ Pr h' β' E) (c y : V) :
    ValH h β c y ↔ ValH h' β c y := by
  rw [valH_iff, valH_iff]
  exact exists_congr fun β' => and_congr_right fun hβ' => exists_congr fun E =>
    and_congr (hag β' hβ' E) Iff.rfl

theorem val1_congr {h h' β : V} (hag : ∀ β', β' ∈ β → ∀ E, Pr h β' E ↔ Pr h' β' E)
    (c x f z0 Cd K0 K1 K2 K3 : V) :
    Val1 h β c x f z0 Cd K0 K1 K2 K3 ↔ Val1 h' β c x f z0 Cd K0 K1 K2 K3 := by
  have e := valH_congr hag
  simp only [Val1, Val2, Kids, e]

theorem gEv_loc (γ h h' E f z0 Cd K0 K1 K2 K3 Ax : V)
    (hag : ∀ β', β' ∈ γ → ∀ E, Pr h β' E ↔ Pr h' β' E)
    (hG : GEv γ h E f z0 Cd K0 K1 K2 K3 Ax) : GEv γ h' E f z0 Cd K0 K1 K2 K3 Ax := by
  have e := val1_congr hag
  simp only [GEv, e] at hG ⊢
  exact hG

theorem gEv_uniq (γ h E E' f z0 Cd K0 K1 K2 K3 Ax : V)
    (hG : GEv γ h E f z0 Cd K0 K1 K2 K3 Ax) (hG' : GEv γ h E' f z0 Cd K0 K1 K2 K3 Ax) :
    E = E' := by
  have key : ∀ E E' : V, GEv γ h E f z0 Cd K0 K1 K2 K3 Ax → GEv γ h E' f z0 Cd K0 K1 K2 K3 Ax →
      ∀ e, e ∈ E → e ∈ E' := by
    intro E E' hG hG' e he
    obtain ⟨c, hc, x, hx, hop, hv⟩ := hG.1 e he
    rw [isOp_iff.mp hop]
    exact pr_iff.mp (hG'.2 c hc x hx hv)
  exact mem_ext fun e => ⟨key E E' hG hG' e, key E' E hG' hG e⟩

theorem val1_iff {h β c x f Cd K0 K1 K2 K3 : V} :
    Val1 h β c x f ∅ Cd K0 K1 K2 K3 ↔ RkC c β ∅ ∧ ∃ A lt, Pr f β (kp A lt) ∧
      Val2 h β c x A lt Cd K0 K1 K2 K3 := and_congr Iff.rfl exAt_iff

theorem exists_isD (A lt s y₁ y₂ y₃ : V) : ∃ x, IsD A lt s y₁ y₂ y₃ x :=
  ⟨sepB (k := 5) (phiB.comp ![1, 0, 2, 3, 4, 5]) A ![lt, s, y₁, y₂, y₃],
    fun z hz => (mem_sepB _ _ _ z).mp hz, fun z hz hp => (mem_sepB _ _ _ z).mpr ⟨hz, hp⟩⟩

theorem rkC_unique {c β β' : V} (hβ : Ord β) (hβ' : Ord β') (h : RkC c β ∅) (h' : RkC c β' ∅) :
    β = β' := by
  rcases ord_tri hβ hβ' with e | e | e
  · exact absurd h.1 (h'.2 β e)
  · exact e
  · exact absurd h'.1 (h.2 β' e)

end bridge

section next

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem funS_apply {E c x x' : V} (hE : FunS E) (h : Pr E c x) (h' : Pr E c x') : x = x' := by
  obtain ⟨e, he, hop⟩ := h
  obtain ⟨e', he', hop'⟩ := h'
  obtain ⟨u, hu, hcu⟩ := pr_fst_mem hop
  obtain ⟨u₁, hu₁, hxu⟩ := pr_snd_mem hop
  obtain ⟨u₂, hu₂, hxu'⟩ := pr_snd_mem hop'
  exact hE e he e' he' u hu c hcu u₁ hu₁ x hxu u₂ hu₂ x' hxu' hop hop'

theorem coded_iff {γ x H : V} : Coded γ x H ↔ ∃ c, ValH H γ c x := by
  constructor
  · rintro ⟨β', hβ', q, hq, u, -, E, -, hop, e, he, u', -, c, -, hop'⟩
    exact ⟨c, valH_iff.mpr ⟨β', hβ', E, ⟨q, hq, hop⟩, ⟨e, he, hop'⟩⟩⟩
  · rintro ⟨c, hc⟩
    obtain ⟨β', hβ', E, ⟨q, hq, hop⟩, ⟨e, he, hop'⟩⟩ := valH_iff.mp hc
    obtain ⟨u, hu, hEu⟩ := pr_snd_mem hop
    obtain ⟨u', hu', hcu⟩ := pr_fst_mem hop'
    exact ⟨β', hβ', q, hq, u, hu, E, hEu, hop, e, he, u', hu', c, hcu, hop'⟩

/-- **The next level is included in the set given by the collapse axiom for the codes.** -/
theorem next_sub {δ β f T A : V} (hδ : Ord δ) (hβ : β ∈ sc δ)
    (hf : IsAtt (k := 0) GMainR ![] f β) (hT : HCat T (CdS (sc δ)))
    (hA : ∀ x, x ∈ A ↔ ∃ β', β' ∈ β ∧ InDefAt f β' x) : ∀ x, x ∈ A → x ∈ T := by
  have hβO : Ord β := ord_mem (ord_sc hδ) hβ
  have hβLb : ∀ β', β' ∈ β → β' ∈ sc δ := fun β' h => (ord_sc hδ).1 β hβ β' h
  -- the levels of `f`
  have flev : ∀ β', β' ∈ β → ∃ A' lt', Pr f β' (kp A' lt') ∧
      ∀ x, x ∈ A' ↔ ∃ β'', β'' ∈ β' ∧ InDefAt f β'' x := by
    intro β' hβ'
    obtain ⟨y, hy, hG⟩ := att_total hf hβ'
    obtain ⟨A', lt', rfl, ha, hb, -, -⟩ := gMain_iff.mp hG
    refine ⟨A', lt', hy, fun x => ⟨ha x, ?_⟩⟩
    rintro ⟨β'', hβ'', hx⟩
    obtain ⟨A₁, lt₁, hf₁, hin⟩ := inDefAt_iff.mp hx
    obtain ⟨hA₁, hcl⟩ := closeAt_iff.mp (hb β'' hβ'') A₁ lt₁ hf₁
    rcases hin with rfl | ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩
    · exact hA₁
    · obtain ⟨x', hx'A, hD'⟩ := hcl s hs y₁ hy₁ y₂ hy₂ y₃ hy₃
      rw [mem_ext (isD_ext hD hD')]
      exact hx'A
  have ffun : ∀ {β' A₁ lt₁ A₂ lt₂ : V}, Pr f β' (kp A₁ lt₁) → Pr f β' (kp A₂ lt₂) →
      A₁ = A₂ ∧ lt₁ = lt₂ := fun h1 h2 => kp_inj (att_fun hf h1 h2)
  have hlevA : ∀ β' A' lt', β' ∈ β → Pr f β' (kp A' lt') → ∀ x, x ∈ A' → x ∈ A := by
    intro β' A' lt' hβ' hpr x hx
    obtain ⟨A₂, lt₂, hpr₂, hA₂⟩ := flev β' hβ'
    obtain ⟨rfl, rfl⟩ := ffun hpr hpr₂
    obtain ⟨β'', hβ'', h⟩ := (hA₂ x).mp hx
    exact (hA x).mpr ⟨β'', hβO.1 β' hβ' β'' hβ'', h⟩
  have hAtr : ∀ x, x ∈ A → ∀ z, z ∈ x → z ∈ A := by
    intro x hx z hz
    obtain ⟨β', hβ', h⟩ := (hA x).mp hx
    obtain ⟨A', lt', hpr, hin⟩ := inDefAt_iff.mp h
    rcases hin with rfl | ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩
    · exact hlevA β' x lt' hβ' hpr z hz
    · exact hlevA β' A' lt' hβ' hpr z (hD.1 z hz).1
  -- the evaluation of the codes
  let Lb : V := sc δ
  let Cd : V := CdS Lb
  let K : Fin 4 → V := fun j => kidS Lb j
  let p : Fin 8 → V := ![f, ∅, Cd, K 0, K 1, K 2, K 3, A]
  have hloc : ∀ γ h h' E : V, Ord γ → (∀ γ', γ' ∈ γ → ∀ y', Pr h γ' y' ↔ Pr h' γ' y') →
      GEvR V (γ :> h :> E :> p) → GEvR V (γ :> h' :> E :> p) := fun γ h h' E _ hag hG =>
    gEv_loc γ h h' E f ∅ Cd (K 0) (K 1) (K 2) (K 3) A hag hG
  have huniq : ∀ γ h E E' : V, GEvR V (γ :> h :> E :> p) → GEvR V (γ :> h :> E' :> p) →
      E = E' := fun γ h E E' hG hG' =>
    gEv_uniq γ h E E' f ∅ Cd (K 0) (K 1) (K 2) (K 3) A hG hG'
  obtain ⟨H, hH⟩ := ord_rec (k := 8) (G := GEvR) gEvB hloc huniq β (℘ (prodS Cd A)) hβO
    (fun β₁ _ h _ _ => by
      let E : V := relB (k := 9) (val1B.comp ![2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10]) Cd A
        ![h, β₁, f, ∅, Cd, K 0, K 1, K 2, K 3]
      have hE : ∀ c x, Pr E c x ↔ c ∈ Cd ∧ x ∈ A ∧
          Val1 h β₁ c x f ∅ Cd (K 0) (K 1) (K 2) (K 3) := fun c x => pr_relB _ _ _ _ c x
      have hEs : ∀ e, e ∈ E → e ∈ prodS Cd A := fun e he => relB_sub _ _ _ _ he
      refine ⟨E, mem_power_iff.mpr hEs, fun e he => ?_,
        fun c hc x hx hv => (hE c x).mpr ⟨hc, hx, hv⟩⟩
      have he' : e ∈ E := he
      obtain ⟨c, hc, x, hx, rfl⟩ := mem_prodS.mp (hEs e he')
      exact ⟨c, hc, x, hx, isOp_kp c x, ((hE c x).mp (pr_iff.mpr he')).2.2⟩)
  have hHfun : ∀ {β' E E' : V}, Pr H β' E → Pr H β' E' → E = E' := fun h1 h2 => att_fun hH h1 h2
  have hEiff : ∀ β' E, Pr H β' E → ∀ c x, Pr E c x ↔ c ∈ Cd ∧ x ∈ A ∧
      Val1 H β' c x f ∅ Cd (K 0) (K 1) (K 2) (K 3) := by
    intro β' E hE c x
    have hG : GEv β' H E f ∅ Cd (K 0) (K 1) (K 2) (K 3) A := att_G hH hE
    constructor
    · rintro ⟨e, he, hop⟩
      obtain ⟨c', hc', x', hx', hop', hv⟩ := hG.1 e he
      obtain ⟨rfl, rfl⟩ := op_inj hop hop'
      exact ⟨hc', hx', hv⟩
    · rintro ⟨hc, hx, hv⟩
      exact hG.2 c hc x hx hv
  have kids_iff : ∀ β' c (y : Fin 4 → V), c ∈ Cd →
      (Kids H β' c (y 0) (y 1) (y 2) (y 3) Cd (K 0) (K 1) (K 2) (K 3) ↔
        ∀ j : Fin 4, ValH H β' (chC Tg4 Lb (nm j) c) (y j)) := by
    intro β' c y hc
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
  -- the values are unique
  have hfunS : ∀ β', β' ∈ β → ∀ E, Pr H β' E → FunS E := by
    by_contra hcon
    let Z : V := sepB (k := 1) (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and
      (funSB.comp ![0]).not)))) β ![H]
    have hZ : ∀ β', β' ∈ Z ↔ β' ∈ β ∧ ∃ q, q ∈ H ∧ ∃ u, u ∈ q ∧ ∃ E, E ∈ u ∧
        (IsOp q β' E ∧ ¬FunS E) := fun β' => mem_sepB _ _ _ β'
    have hne : ∃ β', β' ∈ Z := by
      by_contra h
      refine hcon fun β' hβ' E hE => ?_
      by_contra hn
      obtain ⟨q, hq, hop⟩ := hE
      obtain ⟨u, hu, hEu⟩ := pr_snd_mem hop
      exact h ⟨β', (hZ β').mpr ⟨hβ', q, hq, u, hu, E, hEu, hop, hn⟩⟩
    obtain ⟨β', hβ'Z, hmin⟩ := ord_least Z (fun z hz => ord_mem hβO ((hZ z).mp hz).1) hne
    obtain ⟨hβ', q, hq, u, -, E, -, hop, hnE⟩ := (hZ β').mp hβ'Z
    have hE : Pr H β' E := ⟨q, hq, hop⟩
    have hβ'O : Ord β' := ord_mem hβO hβ'
    have hlow : ∀ c' y y', ValH H β' c' y → ValH H β' c' y' → y = y' := by
      intro c' y y' hy hy'
      obtain ⟨β₁, hβ₁, E₁, hE₁, hp₁⟩ := valH_iff.mp hy
      obtain ⟨β₂, hβ₂, E₂, hE₂, hp₂⟩ := valH_iff.mp hy'
      have hr₁ := (val1_iff.mp ((hEiff β₁ E₁ hE₁ c' y).mp hp₁).2.2).1
      have hr₂ := (val1_iff.mp ((hEiff β₂ E₂ hE₂ c' y').mp hp₂).2.2).1
      have e : β₁ = β₂ := rkC_unique (ord_mem hβ'O hβ₁) (ord_mem hβ'O hβ₂) hr₁ hr₂
      subst e
      have e : E₁ = E₂ := hHfun hE₁ hE₂
      subst e
      have hF₁ : FunS E₁ := by
        by_contra hn
        obtain ⟨q₁, hq₁, hop₁⟩ := hE₁
        obtain ⟨u₁, hu₁, hEu₁⟩ := pr_snd_mem hop₁
        rcases hmin β₁ ((hZ β₁).mpr ⟨hβO.1 β' hβ' β₁ hβ₁, q₁, hq₁, u₁, hu₁, E₁, hEu₁, hop₁, hn⟩)
          with e | e
        · exact mem_irrefl β₁ (e ▸ hβ₁)
        · exact mem_asymm e hβ₁
      exact funS_apply hF₁ hp₁ hp₂
    refine hnE fun e he e' he' u _ c _ u₁ _ x _ u₂ _ x' _ hop hop' => ?_
    obtain ⟨hc, -, hv⟩ := (hEiff β' E hE c x).mp ⟨e, he, hop⟩
    obtain ⟨-, -, hv'⟩ := (hEiff β' E hE c x').mp ⟨e', he', hop'⟩
    obtain ⟨-, A', lt', hpr, hv2⟩ := val1_iff.mp hv
    obtain ⟨-, A'', lt'', hpr', hv2'⟩ := val1_iff.mp hv'
    obtain ⟨rfl, rfl⟩ := ffun hpr hpr'
    rcases hv2 with ⟨y₀, hy₀, y₁, hy₁, y₂, hy₂, y₃, hy₃, hk, hD⟩ | ⟨hno, rfl⟩
    · rcases hv2' with ⟨z₀, hz₀, z₁, hz₁, z₂, hz₂, z₃, hz₃, hk', hD'⟩ | ⟨hno', -⟩
      · have h1 := (kids_iff β' c ![y₀, y₁, y₂, y₃] hc).mp hk
        have h2 := (kids_iff β' c ![z₀, z₁, z₂, z₃] hc).mp hk'
        have e0 : y₀ = z₀ := hlow _ _ _ (h1 0) (h2 0)
        have e1 : y₁ = z₁ := hlow _ _ _ (h1 1) (h2 1)
        have e2 : y₂ = z₂ := hlow _ _ _ (h1 2) (h2 2)
        have e3 : y₃ = z₃ := hlow _ _ _ (h1 3) (h2 3)
        subst e0 e1 e2 e3
        exact mem_ext (isD_ext hD hD')
      · exact absurd ⟨y₀, hy₀, y₁, hy₁, y₂, hy₂, y₃, hy₃, hk⟩ hno'
    · rcases hv2' with ⟨z₀, hz₀, z₁, hz₁, z₂, hz₂, z₃, hz₃, hk', hD'⟩ | ⟨-, e⟩
      · exact absurd ⟨z₀, hz₀, z₁, hz₁, z₂, hz₂, z₃, hz₃, hk'⟩ hno
      · exact e.symm
  have hval_A : ∀ γ c x, ValH H γ c x → c ∈ Cd ∧ x ∈ A := by
    intro γ c x h
    obtain ⟨β₁, -, E₁, hE₁, hp₁⟩ := valH_iff.mp h
    exact ⟨((hEiff β₁ E₁ hE₁ c x).mp hp₁).1, ((hEiff β₁ E₁ hE₁ c x).mp hp₁).2.1⟩
  have hval_fun : ∀ c x x', ValH H β c x → ValH H β c x' → x = x' := by
    intro c x x' hy hy'
    obtain ⟨β₁, hβ₁, E₁, hE₁, hp₁⟩ := valH_iff.mp hy
    obtain ⟨β₂, hβ₂, E₂, hE₂, hp₂⟩ := valH_iff.mp hy'
    have hr₁ := (val1_iff.mp ((hEiff β₁ E₁ hE₁ c x).mp hp₁).2.2).1
    have hr₂ := (val1_iff.mp ((hEiff β₂ E₂ hE₂ c x').mp hp₂).2.2).1
    have e : β₁ = β₂ := rkC_unique (ord_mem hβO hβ₁) (ord_mem hβO hβ₂) hr₁ hr₂
    subst e
    have e : E₁ = E₂ := hHfun hE₁ hE₂
    subst e
    exact funS_apply (hfunS β₁ hβ₁ E₁ hE₁) hp₁ hp₂
  have hemp : (∅ : V) ∈ Cd := mem_power_iff.mpr fun z hz => absurd hz (by simp)
  have hnoval : ∀ γ y, ¬ValH H γ (∅ : V) y := by
    intro γ y h
    obtain ⟨β₁, -, E₁, hE₁, hp₁⟩ := valH_iff.mp h
    have := (val1_iff.mp ((hEiff β₁ E₁ hE₁ ∅ y).mp hp₁).2.2).1.1
    exact absurd (pr_iff.mp this) (by simp)
  -- every member of a level is the value of a code
  have hcoded : ∀ γ, γ ∈ sc β → ∀ x, (∃ β'', β'' ∈ γ ∧ InDefAt f β'' x) → Coded γ x H := by
    by_contra hcon
    let Z : V := sepB (k := 3) (BDef.bex 1 ((BDef.bex 1 (inDefAtB.comp ![4, 0, 1])).and
      (codedB.comp ![1, 0, 4]).not)) (sc β) ![A, f, H]
    have hZ : ∀ γ, γ ∈ Z ↔ γ ∈ sc β ∧ ∃ x, x ∈ A ∧ ((∃ β'', β'' ∈ γ ∧ InDefAt f β'' x) ∧
        ¬Coded γ x H) := fun γ => mem_sepB _ _ _ γ
    have hγβ : ∀ γ, γ ∈ sc β → ∀ β'', β'' ∈ γ → β'' ∈ β := fun γ hγ β'' h => by
      rcases mem_sc.mp hγ with rfl | hγ
      · exact h
      · exact hβO.1 γ hγ β'' h
    have hne : ∃ γ, γ ∈ Z := by
      by_contra h
      refine hcon fun γ hγ x hx => ?_
      by_contra hn
      obtain ⟨β'', hβ'', hin⟩ := hx
      exact h ⟨γ, (hZ γ).mpr ⟨hγ, x, (hA x).mpr ⟨β'', hγβ γ hγ β'' hβ'', hin⟩,
        ⟨β'', hβ'', hin⟩, hn⟩⟩
    obtain ⟨γ, hγZ, hmin⟩ := ord_least Z
      (fun z hz => ord_mem (ord_sc hβO) ((hZ z).mp hz).1) hne
    obtain ⟨hγ, x, hxA, ⟨β'', hβ''γ, hin⟩, hnc⟩ := (hZ γ).mp hγZ
    have hβ''β : β'' ∈ β := hγβ γ hγ β'' hβ''γ
    obtain ⟨A'', lt'', hpr, hinD⟩ := inDefAt_iff.mp hin
    obtain ⟨E'', hE'', -⟩ := att_total hH (mem_sc.mpr (Or.inr hβ''β))
    have hfin : ∀ c, c ∈ Cd → Val1 H β'' c x f ∅ Cd (K 0) (K 1) (K 2) (K 3) → False := by
      intro c hc hv
      have hp : Pr E'' c x := (hEiff β'' E'' hE'' c x).mpr ⟨hc, hxA, hv⟩
      exact hnc (coded_iff.mpr ⟨c, valH_iff.mpr ⟨β'', hβ''γ, E'', hE'', hp⟩⟩)
    have hrk : ∀ cc : Fin 4 → V, RkC (mk4 Lb β'' cc) β'' ∅ := fun cc =>
      ⟨pr_mk4_root.mpr rfl, fun γ' hγ' hp => by
        rw [pr_mk4_root.mp hp] at hγ'
        exact mem_irrefl _ hγ'⟩
    rcases hinD with rfl | ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩
    · -- the level itself: a code whose subtrees have no value
      refine hfin (mk4 Lb β'' (fun _ => ∅)) (mk4_mem (hβLb β'' hβ''β)) (val1_iff.mpr
        ⟨hrk _, x, lt'', hpr, Or.inr ⟨?_, rfl⟩⟩)
      rintro ⟨y₀, -, y₁, -, y₂, -, y₃, -, hk⟩
      have := (kids_iff β'' _ ![y₀, y₁, y₂, y₃] (mk4_mem (hβLb β'' hβ''β))).mp hk 0
      rw [chC_mk4 (fun _ => hemp) 0] at this
      exact hnoval _ _ this
    · -- a definable set: codes for the parameters
      have hpar : ∀ a, a ∈ A'' → ∃ c, ValH H β'' c a := by
        intro a ha
        obtain ⟨A₂, lt₂, hpr₂, hA₂⟩ := flev β'' hβ''β
        obtain ⟨rfl, rfl⟩ := ffun hpr hpr₂
        have hcd : Coded β'' a H := by
          by_contra hn
          rcases hmin β'' ((hZ β'').mpr ⟨mem_sc.mpr (Or.inr hβ''β), a,
            hlevA β'' A'' lt'' hβ''β hpr a ha, (hA₂ a).mp ha, hn⟩) with e | e
          · exact mem_irrefl β'' (e ▸ hβ''γ)
          · exact mem_asymm e hβ''γ
        exact coded_iff.mp hcd
      obtain ⟨c₀, hc₀⟩ := hpar s hs
      obtain ⟨c₁, hc₁⟩ := hpar y₁ hy₁
      obtain ⟨c₂, hc₂⟩ := hpar y₂ hy₂
      obtain ⟨c₃, hc₃⟩ := hpar y₃ hy₃
      have hcc : ∀ j : Fin 4, (![c₀, c₁, c₂, c₃] : Fin 4 → V) j ∈ Cd := fun j => by
        match j with
        | 0 => exact (hval_A _ _ _ hc₀).1
        | 1 => exact (hval_A _ _ _ hc₁).1
        | 2 => exact (hval_A _ _ _ hc₂).1
        | 3 => exact (hval_A _ _ _ hc₃).1
      refine hfin (mk4 Lb β'' ![c₀, c₁, c₂, c₃]) (mk4_mem (hβLb β'' hβ''β)) (val1_iff.mpr
        ⟨hrk _, A'', lt'', hpr, Or.inl ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, ?_, hD⟩⟩)
      refine (kids_iff β'' _ ![s, y₁, y₂, y₃] (mk4_mem (hβLb β'' hβ''β))).mpr fun j => ?_
      rw [chC_mk4 hcc j]
      match j with
      | 0 => exact hc₀
      | 1 => exact hc₁
      | 2 => exact hc₂
      | 3 => exact hc₃
  -- the collapse
  let r : V := relB (k := 3) (BDef.bex 4 (BDef.bex 0 ((valHB.comp ![4, 5, 3, 1]).and
    (valHB.comp ![4, 5, 2, 0])))) Cd Cd ![H, β, A]
  have hr : ∀ c' c, Pr r c' c ↔ c' ∈ Cd ∧ c ∈ Cd ∧ ∃ x, x ∈ A ∧ ∃ x', x' ∈ x ∧
      (ValH H β c x ∧ ValH H β c' x') := fun c' c => pr_relB _ _ _ _ c' c
  have hwf : WFon r Cd := by
    rintro X ⟨c₀, hc₀, -⟩ -
    let S : V := sepB (k := 3) (BDef.bex 1 (valHB.comp ![3, 4, 0, 1])) A ![X, H, β]
    have hS : ∀ x, x ∈ S ↔ x ∈ A ∧ ∃ c, c ∈ X ∧ ValH H β c x := fun x => mem_sepB _ _ _ x
    by_cases hne : ∃ x, x ∈ S
    · obtain ⟨x₀, hx₀, hmin⟩ := m_found S hne
      obtain ⟨-, c, hcX, hcv⟩ := (hS x₀).mp hx₀
      refine ⟨c, hcX, fun c' hc' hrc => ?_⟩
      obtain ⟨-, -, x, -, x', hx'x, hv, hv'⟩ := (hr c' c).mp hrc
      have e : x = x₀ := hval_fun c x x₀ hv hcv
      subst e
      exact hmin x' ((hS x').mpr ⟨(hval_A _ c' x' hv').2, c', hc', hv'⟩) hx'x
    · refine ⟨c₀, hc₀, fun c' _ hrc => hne ?_⟩
      obtain ⟨-, -, x, hxA, x', -, hv, -⟩ := (hr c' c₀).mp hrc
      exact ⟨x, (hS x).mpr ⟨hxA, c₀, hc₀, hv⟩⟩
  obtain ⟨F, hF⟩ := hT.2 r hwf
  have hFval : ∀ c x, ValH H β c x → Pr F c x := by
    by_contra hcon
    let Z : V := sepB (k := 4) (BDef.bex 1 ((valHB.comp ![3, 4, 0, 1]).and
      (prB.comp ![5, 0, 1]).not)) A ![Cd, H, β, F]
    have hZ : ∀ x, x ∈ Z ↔ x ∈ A ∧ ∃ c, c ∈ Cd ∧ (ValH H β c x ∧ ¬Pr F c x) :=
      fun x => mem_sepB _ _ _ x
    have hne : ∃ x, x ∈ Z := by
      by_contra h
      refine hcon fun c x hv => ?_
      by_contra hn
      exact h ⟨x, (hZ x).mpr ⟨(hval_A _ c x hv).2, c, (hval_A _ c x hv).1, hv, hn⟩⟩
    obtain ⟨x, hxZ, hmin⟩ := m_found Z hne
    obtain ⟨hxA, c, hc, hcx, hnF⟩ := (hZ x).mp hxZ
    obtain ⟨v, -, hcv, -, hvm⟩ := hF c hc
    have e : v = x := mem_ext fun y => by
      rw [hvm]
      constructor
      · rintro ⟨c', hc', hrc, hFc'⟩
        obtain ⟨-, -, x₁, -, x', hx'x₁, hv₁, hv'⟩ := (hr c' c).mp hrc
        have e : x₁ = x := hval_fun c x₁ x hv₁ hcx
        subst e
        have hFx' : Pr F c' x' := by
          by_contra hn
          exact hmin x' ((hZ x').mpr ⟨(hval_A _ c' x' hv').2, c', hc', hv', hn⟩) hx'x₁
        obtain ⟨v', -, -, hv'u, -⟩ := hF c' hc'
        rw [hv'u y hFc', ← hv'u x' hFx']
        exact hx'x₁
      · intro hy
        have hyA : y ∈ A := hAtr x hxA y hy
        obtain ⟨c', hc'v⟩ := coded_iff.mp (hcoded β (self_mem_sc β) y ((hA y).mp hyA))
        have hc'Cd := (hval_A _ c' y hc'v).1
        have hFy : Pr F c' y := by
          by_contra hn
          exact hmin y ((hZ y).mpr ⟨hyA, c', hc'Cd, hc'v, hn⟩) hy
        exact ⟨c', hc'Cd, (hr c' c).mpr ⟨hc'Cd, hc, x, hxA, y, hy, hcx, hc'v⟩, hFy⟩
    exact hnF (e ▸ hcv)
  intro x hx
  obtain ⟨c, hcv⟩ := coded_iff.mp (hcoded β (self_mem_sc β) x ((hA x).mp hx))
  obtain ⟨v, hvT, -, hvu, -⟩ := hF c (hval_A _ c x hcv).1
  rw [hvu x (hFval c x hcv)]
  exact hvT

end next

section exist

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **For every ordinal there is a sequence of the levels up to it.** -/
theorem exists_hier {δ : V} (hδ : Ord δ) : ∃ F, IsHier F δ := by
  obtain ⟨T, hT⟩ := hc_of_models (V := V) (CdS (sc δ))
  let C : V := prodS (℘ T) (℘ (prodS T T))
  refine ord_rec (k := 0) (G := GMainR) gMainB gMainR_loc gMainR_uniq δ C hδ
    (fun β hβ f hfPC hf => ?_)
  have hsubT : ∀ β' A' lt', Pr f β' (kp A' lt') → ∀ x, x ∈ A' → x ∈ T := by
    intro β' A' lt' hpr x hx
    have h1 := mem_power_iff.mp hfPC _ (pr_iff.mp hpr)
    obtain ⟨a, -, b, hb, e⟩ := mem_prodS.mp h1
    obtain ⟨-, rfl⟩ := kp_inj e
    obtain ⟨a', ha', b', -, e'⟩ := mem_prodS.mp hb
    obtain ⟨rfl, -⟩ := kp_inj e'
    exact mem_power_iff.mp ha' x hx
  let A : V := sepB (k := 2) (BDef.bex 1 (inDefAtB.comp ![3, 0, 1])) (℘ T) ![β, f]
  have hA0 : ∀ x, x ∈ A ↔ x ∈ ℘ T ∧ ∃ β', β' ∈ β ∧ InDefAt f β' x := fun x => mem_sepB _ _ _ x
  have hA : ∀ x, x ∈ A ↔ ∃ β', β' ∈ β ∧ InDefAt f β' x := by
    intro x
    refine (hA0 x).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨β', hβ', hin⟩ := h
    obtain ⟨A', lt', hpr, hd⟩ := inDefAt_iff.mp hin
    refine mem_power_iff.mpr fun z hz => ?_
    rcases hd with rfl | ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩
    · exact hsubT β' x lt' hpr z hz
    · exact hsubT β' A' lt' hpr z (hD.1 z hz).1
  have hAT : ∀ x, x ∈ A → x ∈ T := next_sub hδ hβ hf hT hA
  let lt : V := relB (k := 2) (keyLessB.comp ![2, 3, 0, 1]) A A ![f, β]
  have hlt : ∀ x x', Pr lt x x' ↔ x ∈ A ∧ x' ∈ A ∧ KeyLess f β x x' :=
    fun x x' => pr_relB _ _ _ _ x x'
  have hltsub : ∀ q, q ∈ lt → q ∈ prodS A A := fun q hq => relB_sub _ _ _ _ hq
  refine ⟨kp A lt, mem_prodS.mpr ⟨A, mem_power_iff.mpr hAT, lt,
    mem_power_iff.mpr (fun q hq => ?_), rfl⟩, ?_⟩
  · obtain ⟨x, hx, x', hx', rfl⟩ := mem_prodS.mp (hltsub q hq)
    exact mem_prodS.mpr ⟨x, hAT x hx, x', hAT x' hx', rfl⟩
  · show GMain β f (kp A lt)
    refine gMain_iff.mpr ⟨A, lt, rfl, fun x hx => (hA x).mp hx, fun β' hβ' => ?_,
      fun q hq => ?_, fun x hx x' hx' => ?_⟩
    · refine closeAt_iff.mpr fun A' lt' hpr => ⟨(hA A').mpr ⟨β', hβ',
        inDefAt_iff.mpr ⟨A', lt', hpr, Or.inl rfl⟩⟩, fun s hs y₁ hy₁ y₂ hy₂ y₃ hy₃ => ?_⟩
      obtain ⟨x, hx⟩ := exists_isD A' lt' s y₁ y₂ y₃
      exact ⟨x, (hA x).mpr ⟨β', hβ', inDefAt_iff.mpr ⟨A', lt', hpr,
        Or.inr ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hx⟩⟩⟩, hx⟩
    · obtain ⟨x, hx, x', hx', rfl⟩ := mem_prodS.mp (hltsub q hq)
      exact ⟨x, hx, x', hx', isOp_kp x x'⟩
    · exact ⟨fun h => ((hlt x x').mp h).2.2, fun h => (hlt x x').mpr ⟨hx, hx', h⟩⟩

theorem exists_dat {γ : V} (hγ : Ord γ) : ∃ A lt, ∃ F, IsHier F γ ∧ Pr F γ (kp A lt) := by
  obtain ⟨F, hF⟩ := exists_hier hγ
  obtain ⟨A, lt, hpr, -⟩ := hier_at hF (self_mem_sc γ)
  exact ⟨A, lt, F, hF, hpr⟩

open Classical in
/-- **The level at the ordinal `γ`.** -/
noncomputable def Lev (γ : V) : V := if h : Ord γ then Classical.choose (exists_dat h) else ∅

open Classical in
/-- The order of the level at `γ`, as a set of pairs. -/
noncomputable def LtS (γ : V) : V :=
  if h : Ord γ then Classical.choose (Classical.choose_spec (exists_dat h)) else ∅

theorem hier_lev {F δ γ : V} (hδ : Ord δ) (hF : IsHier F δ) (hγ : γ ∈ sc δ) :
    Pr F γ (kp (Lev γ) (LtS γ)) := by
  have hγO : Ord γ := ord_mem (ord_sc hδ) hγ
  obtain ⟨F', hF', hpr⟩ := Classical.choose_spec (Classical.choose_spec (exists_dat hγO))
  have h1 : Pr F' γ (kp (Lev γ) (LtS γ)) := by
    rw [Lev, LtS, dif_pos hγO, dif_pos hγO]
    exact hpr
  exact (hier_agree hγO hδ hF' hF (self_mem_sc γ) hγ _).mp h1

theorem hier_lev_eq {F δ γ A lt : V} (hδ : Ord δ) (hF : IsHier F δ) (hγ : γ ∈ sc δ)
    (h : Pr F γ (kp A lt)) : A = Lev γ ∧ lt = LtS γ := hier_fun hF h (hier_lev hδ hF hγ)

theorem inDefAt_lev {F δ γ x : V} (hδ : Ord δ) (hF : IsHier F δ) (hγ : γ ∈ sc δ) :
    InDefAt F γ x ↔ InDef (Lev γ) (LtS γ) x := by
  rw [inDefAt_iff]
  constructor
  · rintro ⟨A, lt, hpr, h⟩
    obtain ⟨rfl, rfl⟩ := hier_lev_eq hδ hF hγ hpr
    exact h
  · intro h
    exact ⟨_, _, hier_lev hδ hF hγ, h⟩

/-- **The members of a level** are the sets definable over an earlier level. -/
theorem mem_lev {γ x : V} (hγ : Ord γ) :
    x ∈ Lev γ ↔ ∃ β, β ∈ γ ∧ InDef (Lev β) (LtS β) x := by
  obtain ⟨F, hF⟩ := exists_hier hγ
  obtain ⟨A, lt, hpr, ha, hb, -, -⟩ := hier_at hF (self_mem_sc γ)
  obtain ⟨rfl, rfl⟩ := hier_lev_eq hγ hF (self_mem_sc γ) hpr
  constructor
  · intro hx
    obtain ⟨β, hβ, h⟩ := ha x hx
    exact ⟨β, hβ, (inDefAt_lev hγ hF (mem_sc.mpr (Or.inr hβ))).mp h⟩
  · rintro ⟨β, hβ, h⟩
    obtain ⟨hA₁, hcl⟩ := closeAt_iff.mp (hb β hβ) _ _ (hier_lev hγ hF (mem_sc.mpr (Or.inr hβ)))
    rcases h with rfl | ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩
    · exact hA₁
    · obtain ⟨x', hx'A, hD'⟩ := hcl s hs y₁ hy₁ y₂ hy₂ y₃ hy₃
      rw [mem_ext (isD_ext hD hD')]
      exact hx'A

theorem lev_mono {β γ : V} (hγ : Ord γ) (hβ : β ∈ γ) : ∀ x, x ∈ Lev β → x ∈ Lev γ := by
  intro x hx
  obtain ⟨β', hβ', h⟩ := (mem_lev (ord_mem hγ hβ)).mp hx
  exact (mem_lev hγ).mpr ⟨β', hγ.1 β hβ β' hβ', h⟩

theorem lev_mem {β γ : V} (hγ : Ord γ) (hβ : β ∈ γ) : Lev β ∈ Lev γ :=
  (mem_lev hγ).mpr ⟨β, hβ, Or.inl rfl⟩

theorem lev_tr {γ : V} (hγ : Ord γ) : Tr (Lev γ) := by
  intro x hx z hz
  obtain ⟨β, hβ, h⟩ := (mem_lev hγ).mp hx
  rcases h with rfl | ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩
  · exact lev_mono hγ hβ z hz
  · exact lev_mono hγ hβ z (hD.1 z hz).1

/-- A set defined over the level at `β` with parameters in it is a member of the later
levels. -/
theorem def_mem_lev {β γ s y₁ y₂ y₃ x : V} (hγ : Ord γ) (hβ : β ∈ γ) (hs : s ∈ Lev β)
    (hy₁ : y₁ ∈ Lev β) (hy₂ : y₂ ∈ Lev β) (hy₃ : y₃ ∈ Lev β)
    (hD : IsD (Lev β) (LtS β) s y₁ y₂ y₃ x) : x ∈ Lev γ :=
  (mem_lev hγ).mpr ⟨β, hβ, Or.inr ⟨s, hs, y₁, hy₁, y₂, hy₂, y₃, hy₃, hD⟩⟩

theorem lev_sub_of_le {β γ : V} (hβ : Ord β) (hγ : Ord γ) (h : β = γ ∨ β ∈ γ) :
    ∀ x, x ∈ Lev β → x ∈ Lev γ := by
  rcases h with rfl | h
  · exact fun x hx => hx
  · exact lev_mono hγ h

end exist

end MH

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.exists_hier
