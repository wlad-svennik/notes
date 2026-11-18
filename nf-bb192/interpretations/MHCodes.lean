import MHLevels

set_option autoImplicit false

/-!
# Codes

Inside a model `V` of `𝗠`. A *code* is a tree with four branches at every node, each node
carrying labels: formally a set of pairs `⟨w, x⟩` of an address `w` and a label `x`. An address
is a set of pairs `⟨n, i⟩` with `n ∈ ω` and `i` one of four tags; the root is the empty set, and
the `J`-th child of `w` is `{⟨0, J⟩} ∪ {⟨n + 1, i⟩ : ⟨n, i⟩ ∈ w}`. So all codes with labels in a
set `Lb` are subsets of one set, whatever their depth.

* `chA`: the child of an address. `chC`: the subtree at a child of the root.
* `mkC β c₀ c₁ c₂ c₃`: the tree with root label `β` and the four given subtrees.
  `chC_mkC`, `pr_mkC_root`.

Codes are used only to show that every level is the image of one fixed set, so that the
collapse axiom keeps all the levels inside one set (`MHExist.lean`).
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section defs

variable {V : Type} [SetStructure V]

/-- `q = ⟨n, i⟩` and `p = ⟨n + 1, i⟩`. -/
def ShiftP (p q : V) : Prop :=
  ∃ u, u ∈ q ∧ ∃ n, n ∈ u ∧ ∃ u₁, u₁ ∈ q ∧ ∃ i, i ∈ u₁ ∧ ∃ u', u' ∈ p ∧ ∃ n', n' ∈ u' ∧
    (IsOp q n i ∧ (IsOp p n' i ∧ SuccR n' n))

/-- `w'` is the `J`-th child of the address `w`; `z0` is the empty set. -/
def ChAddr (w' w J z0 : V) : Prop :=
  Pr w' z0 J ∧ ((∀ p, p ∈ w' → IsOp p z0 J ∨ ∃ q, q ∈ w ∧ ShiftP p q) ∧
    (∀ q, q ∈ w → ∃ p, p ∈ w' ∧ ShiftP p q))

/-- `β` is the least label of `c` at the root. -/
def RkC (c β z0 : V) : Prop := Pr c z0 β ∧ ∀ γ, γ ∈ β → ¬Pr c z0 γ

/-- `c'` is the subtree of `c` at the `J`-th child of the root. -/
def IsChild (c c' J z0 AU Lb : V) : Prop :=
  (∀ e', e' ∈ c' → ∃ w, w ∈ AU ∧ ∃ x, x ∈ Lb ∧ ∃ w', w' ∈ AU ∧
    (IsOp e' w x ∧ (ChAddr w' w J z0 ∧ Pr c w' x))) ∧
  (∀ w, w ∈ AU → ∀ x, x ∈ Lb → ∀ w', w' ∈ AU → ChAddr w' w J z0 → Pr c w' x → Pr c' w x)

end defs

def shiftPB : BDef (k := 2) (fun V _ v ↦ ShiftP (v 0) (v 1)) :=
  (BDef.bex 1 (BDef.bex 0 (BDef.bex 3 (BDef.bex 0 (BDef.bex 4 (BDef.bex 0
    ((isOpB.comp ![7, 4, 2]).and ((isOpB.comp ![6, 0, 2]).and
      (succB.comp ![0, 4]))))))))).congr fun _ _ _ => Iff.rfl

def chAddrB : BDef (k := 4) (fun V _ v ↦ ChAddr (v 0) (v 1) (v 2) (v 3)) :=
  ((prB.comp ![0, 3, 2]).and ((BDef.ball 0 ((isOpB.comp ![0, 4, 3]).or
    (BDef.bex 2 (shiftPB.comp ![1, 0])))).and
    (BDef.ball 1 (BDef.bex 1 (shiftPB.comp ![0, 1]))))).congr fun _ _ _ => Iff.rfl

def rkCB : BDef (k := 3) (fun V _ v ↦ RkC (v 0) (v 1) (v 2)) :=
  ((prB.comp ![0, 2, 1]).and (BDef.ball 1 (prB.comp ![1, 3, 0]).not)).congr fun _ _ _ => Iff.rfl

def isChildB : BDef (k := 6)
    (fun V _ v ↦ IsChild (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  ((BDef.ball 1 (BDef.bex 5 (BDef.bex 7 (BDef.bex 7 ((isOpB.comp ![3, 2, 1]).and
    ((chAddrB.comp ![0, 2, 6, 7]).and (prB.comp ![4, 0, 1]))))))).and
    (BDef.ball 4 (BDef.ball 6 (BDef.ball 6 ((chAddrB.comp ![0, 2, 5, 6]).imp
      ((prB.comp ![3, 0, 1]).imp (prB.comp ![4, 2, 1]))))))).congr fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem sc_ne_empty (n : V) : sc n ≠ ∅ := fun h => by
  have := self_mem_sc n
  rw [h] at this
  exact absurd this (by simp)

theorem sc_inj {n m : V} (h : sc n = sc m) : n = m := by
  have h1 : n ∈ sc m := h ▸ self_mem_sc n
  have h2 : m ∈ sc n := h.symm ▸ self_mem_sc m
  rcases mem_sc.mp h1 with e | h1
  · exact e
  · rcases mem_sc.mp h2 with e | h2
    · exact e.symm
    · exact absurd h2 (mem_asymm h1)

theorem relB_sub {k : ℕ} {R : MRel (k + 2)} (d : BDef R) (a b : V) (p : Fin k → V) {z : V}
    (h : z ∈ relB d a b p) : z ∈ prodS a b := ((mem_sepB _ _ _ z).mp h).1

theorem shiftP_iff {p q : V} : ShiftP p q ↔ ∃ n i, q = kp n i ∧ p = kp (sc n) i := by
  constructor
  · rintro ⟨u, -, n, -, u₁, -, i, -, u', -, n', -, h1, h2, h3⟩
    exact ⟨n, i, isOp_iff.mp h1, succR_iff_sc.mp h3 ▸ isOp_iff.mp h2⟩
  · rintro ⟨n, i, rfl, rfl⟩
    obtain ⟨u, hu, hnu⟩ := pr_fst_mem (isOp_kp n i)
    obtain ⟨u₁, hu₁, hiu⟩ := pr_snd_mem (isOp_kp n i)
    obtain ⟨u', hu', hnu'⟩ := pr_fst_mem (isOp_kp (sc n) i)
    exact ⟨u, hu, n, hnu, u₁, hu₁, i, hiu, u', hu', sc n, hnu', isOp_kp n i, isOp_kp (sc n) i,
      succR_iff_sc.mpr rfl⟩

/-- The set of the addresses with tags in `Tg`. -/
noncomputable def AUset (Tg : V) : V := ℘ (prodS (om : V) Tg)

/-- The `J`-th child of the address `w`. -/
noncomputable def chA (Tg J w : V) : V :=
  insert (kp ∅ J) (sepB (k := 1) (BDef.bex 1 (shiftPB.comp ![1, 0])) (prodS (om : V) Tg) ![w])

theorem mem_chA {Tg J w p : V} (hw : w ∈ AUset Tg) :
    p ∈ chA Tg J w ↔ p = kp ∅ J ∨ ∃ n i, kp n i ∈ w ∧ p = kp (sc n) i := by
  have hw' : ∀ q, q ∈ w → q ∈ prodS (om : V) Tg := mem_power_iff.mp hw
  simp only [chA, mem_insert]
  refine or_congr Iff.rfl ?_
  constructor
  · intro h
    obtain ⟨-, q, hq, hs⟩ := (mem_sepB _ _ _ p).mp h
    obtain ⟨n, i, rfl, rfl⟩ := shiftP_iff.mp hs
    exact ⟨n, i, hq, rfl⟩
  · rintro ⟨n, i, hq, rfl⟩
    obtain ⟨n', hn', i', hi', e⟩ := mem_prodS.mp (hw' _ hq)
    obtain ⟨rfl, rfl⟩ := kp_inj e
    exact (mem_sepB _ _ _ _).mpr ⟨mem_prodS.mpr ⟨sc n, sc_mem_om hn', i, hi', rfl⟩, kp n i, hq,
      shiftP_iff.mpr ⟨n, i, rfl, rfl⟩⟩

theorem chA_mem {Tg J w : V} (hJ : J ∈ Tg) (hw : w ∈ AUset Tg) : chA Tg J w ∈ AUset Tg := by
  have hw' : ∀ q, q ∈ w → q ∈ prodS (om : V) Tg := mem_power_iff.mp hw
  refine mem_power_iff.mpr fun p hp => ?_
  rcases (mem_chA hw).mp hp with rfl | ⟨n, i, hq, rfl⟩
  · exact mem_prodS.mpr ⟨∅, empty_mem_om, J, hJ, rfl⟩
  · obtain ⟨n', hn', i', hi', e⟩ := mem_prodS.mp (hw' _ hq)
    obtain ⟨rfl, rfl⟩ := kp_inj e
    exact mem_prodS.mpr ⟨sc n, sc_mem_om hn', i, hi', rfl⟩

theorem chA_ne_empty {Tg J w : V} : chA Tg J w ≠ ∅ := fun h => by
  have : kp ∅ J ∈ chA Tg J w := by simp [chA]
  rw [h] at this
  exact absurd this (by simp)

theorem chAddr_iff {Tg J w w' : V} (hw : w ∈ AUset Tg) :
    ChAddr w' w J ∅ ↔ w' = chA Tg J w := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine mem_ext fun p => (Iff.trans ?_ (mem_chA hw).symm)
    constructor
    · intro hp
      rcases h2 p hp with h | ⟨q, hq, hs⟩
      · exact Or.inl (isOp_iff.mp h)
      · obtain ⟨n, i, rfl, rfl⟩ := shiftP_iff.mp hs
        exact Or.inr ⟨n, i, hq, rfl⟩
    · rintro (rfl | ⟨n, i, hq, rfl⟩)
      · exact pr_iff.mp h1
      · obtain ⟨p', hp', hs⟩ := h3 _ hq
        obtain ⟨n', i', e, rfl⟩ := shiftP_iff.mp hs
        obtain ⟨rfl, rfl⟩ := kp_inj e
        exact hp'
  · rintro rfl
    refine ⟨pr_iff.mpr ((mem_chA hw).mpr (Or.inl rfl)), fun p hp => ?_, fun q hq => ?_⟩
    · rcases (mem_chA hw).mp hp with rfl | ⟨n, i, hq, rfl⟩
      · exact Or.inl (isOp_kp _ _)
      · exact Or.inr ⟨_, hq, shiftP_iff.mpr ⟨n, i, rfl, rfl⟩⟩
    · obtain ⟨n, hn, i, hi, rfl⟩ := mem_prodS.mp (mem_power_iff.mp hw q hq)
      exact ⟨kp (sc n) i, (mem_chA hw).mpr (Or.inr ⟨n, i, hq, rfl⟩), shiftP_iff.mpr ⟨n, i, rfl, rfl⟩⟩

theorem chA_inj {Tg J J' w w' : V} (hw : w ∈ AUset Tg) (hw' : w' ∈ AUset Tg)
    (h : chA Tg J w = chA Tg J' w') : J = J' ∧ w = w' := by
  have hJ : J = J' := by
    have : kp ∅ J ∈ chA Tg J' w' := h ▸ (mem_chA hw).mpr (Or.inl rfl)
    rcases (mem_chA hw').mp this with e | ⟨n, i, -, e⟩
    · exact (kp_inj e).2
    · exact absurd (kp_inj e).1.symm (sc_ne_empty n)
  subst hJ
  have key : ∀ w w' : V, w ∈ AUset Tg → w' ∈ AUset Tg → chA Tg J w = chA Tg J w' →
      ∀ q, q ∈ w → q ∈ w' := by
    intro w w' hw hw' h q hq
    obtain ⟨n, hn, i, hi, rfl⟩ := mem_prodS.mp (mem_power_iff.mp hw q hq)
    have : kp (sc n) i ∈ chA Tg J w' := h ▸ (mem_chA hw).mpr (Or.inr ⟨n, i, hq, rfl⟩)
    rcases (mem_chA hw').mp this with e | ⟨n', i', hq', e⟩
    · exact absurd (kp_inj e).1 (sc_ne_empty n)
    · obtain ⟨e1, rfl⟩ := kp_inj e
      rw [sc_inj e1]
      exact hq'
  exact ⟨rfl, mem_ext fun q => ⟨key w w' hw hw' h q, key w' w hw' hw h.symm q⟩⟩

/-- The subtree of `c` at the `J`-th child of the root. -/
noncomputable def chC (Tg Lb J c : V) : V :=
  relB (k := 4) (BDef.bex 5 ((chAddrB.comp ![0, 1, 4, 5]).and (prB.comp ![3, 0, 2])))
    (AUset Tg) Lb ![c, J, ∅, AUset Tg]

theorem pr_chC {Tg Lb J c w x : V} (hJ : J ∈ Tg) :
    Pr (chC Tg Lb J c) w x ↔ w ∈ AUset Tg ∧ x ∈ Lb ∧ Pr c (chA Tg J w) x := by
  refine (pr_relB _ _ _ _ w x).trans (and_congr_right fun hw => and_congr_right fun _ => ?_)
  constructor
  · rintro ⟨w', -, hch, hpr⟩
    have hch' : ChAddr w' w J ∅ := hch
    have hpr' : Pr c w' x := hpr
    rw [← (chAddr_iff hw).mp hch']
    exact hpr'
  · intro h
    exact ⟨chA Tg J w, chA_mem hJ hw, (chAddr_iff hw).mpr rfl, h⟩

theorem chC_mem {Tg Lb J c : V} : chC Tg Lb J c ∈ ℘ (prodS (AUset Tg) Lb) :=
  mem_power_iff.mpr fun _ h => relB_sub _ _ _ _ h

theorem isChild_iff {Tg Lb J c c' : V} (hJ : J ∈ Tg) (hc' : c' ∈ ℘ (prodS (AUset Tg) Lb)) :
    IsChild c c' J ∅ (AUset Tg) Lb ↔ c' = chC Tg Lb J c := by
  constructor
  · rintro ⟨h1, h2⟩
    refine mem_ext fun e => ⟨fun he => ?_, fun he => ?_⟩
    · obtain ⟨w, hw, x, hx, w', -, hop, hch, hpr⟩ := h1 e he
      rw [isOp_iff.mp hop]
      refine pr_iff.mp ((pr_chC hJ).mpr ⟨hw, hx, ?_⟩)
      rw [← (chAddr_iff hw).mp hch]
      exact hpr
    · obtain ⟨w, hw, x, hx, rfl⟩ := mem_prodS.mp (relB_sub _ _ _ _ he)
      obtain ⟨-, -, hpr⟩ := (pr_chC hJ).mp (pr_iff.mpr he)
      exact pr_iff.mp (h2 w hw x hx _ (chA_mem hJ hw) ((chAddr_iff hw).mpr rfl) hpr)
  · rintro rfl
    refine ⟨fun e he => ?_, fun w hw x hx w' _ hch hpr => ?_⟩
    · obtain ⟨w, hw, x, hx, rfl⟩ := mem_prodS.mp (relB_sub _ _ _ _ he)
      obtain ⟨-, -, hpr⟩ := (pr_chC hJ).mp (pr_iff.mpr he)
      exact ⟨w, hw, x, hx, _, chA_mem hJ hw, isOp_kp w x, (chAddr_iff hw).mpr rfl, hpr⟩
    · refine (pr_chC hJ).mpr ⟨hw, hx, ?_⟩
      rw [← (chAddr_iff hw).mp hch]
      exact hpr

/-- The pairs `⟨J-th child of w, x⟩` for `⟨w, x⟩ ∈ c`. -/
noncomputable def graft (Tg Lb J c : V) : V :=
  relB (k := 4) (BDef.bex 5 ((chAddrB.comp ![1, 0, 4, 5]).and (prB.comp ![3, 0, 2])))
    (AUset Tg) Lb ![c, J, ∅, AUset Tg]

theorem pr_graft {Tg Lb J c w' x : V} :
    Pr (graft Tg Lb J c) w' x ↔ w' ∈ AUset Tg ∧ x ∈ Lb ∧
      ∃ w, w ∈ AUset Tg ∧ w' = chA Tg J w ∧ Pr c w x := by
  refine (pr_relB _ _ _ _ w' x).trans (and_congr_right fun _ => and_congr_right fun _ => ?_)
  constructor
  · rintro ⟨w, hw, hch, hpr⟩
    exact ⟨w, hw, (chAddr_iff hw).mp hch, hpr⟩
  · rintro ⟨w, hw, rfl, hpr⟩
    exact ⟨w, hw, (chAddr_iff hw).mpr rfl, hpr⟩

/-- The tree with root label `β` and the four subtrees `c₀, …, c₃` at the children with tags
`J₀, …, J₃`. -/
noncomputable def mkC (Tg Lb β J₀ J₁ J₂ J₃ c₀ c₁ c₂ c₃ : V) : V :=
  insert (kp ∅ β) (graft Tg Lb J₀ c₀ ∪ (graft Tg Lb J₁ c₁ ∪ (graft Tg Lb J₂ c₂ ∪
    graft Tg Lb J₃ c₃)))

theorem pr_mkC {Tg Lb β J₀ J₁ J₂ J₃ c₀ c₁ c₂ c₃ w x : V} :
    Pr (mkC Tg Lb β J₀ J₁ J₂ J₃ c₀ c₁ c₂ c₃) w x ↔ (w = ∅ ∧ x = β) ∨
      (Pr (graft Tg Lb J₀ c₀) w x ∨ (Pr (graft Tg Lb J₁ c₁) w x ∨
        (Pr (graft Tg Lb J₂ c₂) w x ∨ Pr (graft Tg Lb J₃ c₃) w x))) := by
  simp only [pr_iff, mkC, mem_insert, mem_union_iff]
  exact or_congr ⟨fun e => kp_inj e, fun ⟨e1, e2⟩ => by rw [e1, e2]⟩ Iff.rfl

theorem pr_mkC_root {Tg Lb β J₀ J₁ J₂ J₃ c₀ c₁ c₂ c₃ γ : V} :
    Pr (mkC Tg Lb β J₀ J₁ J₂ J₃ c₀ c₁ c₂ c₃) ∅ γ ↔ γ = β := by
  rw [pr_mkC]
  constructor
  · rintro (⟨-, e⟩ | h | h | h | h)
    · exact e
    all_goals
      obtain ⟨-, -, w, -, e, -⟩ := pr_graft.mp h
      exact absurd e.symm chA_ne_empty
  · intro e
    exact Or.inl ⟨rfl, e⟩

theorem mkC_mem {Tg Lb β J₀ J₁ J₂ J₃ c₀ c₁ c₂ c₃ : V} (hβ : β ∈ Lb) :
    mkC Tg Lb β J₀ J₁ J₂ J₃ c₀ c₁ c₂ c₃ ∈ ℘ (prodS (AUset Tg) Lb) := by
  refine mem_power_iff.mpr fun e he => ?_
  simp only [mkC, mem_insert, mem_union_iff] at he
  rcases he with rfl | h | h | h | h
  · exact mem_prodS.mpr ⟨∅, mem_power_iff.mpr (fun z hz => absurd hz (by simp)), β, hβ, rfl⟩
  all_goals exact relB_sub _ _ _ _ h

/-! ### Numerals, and the four tags -/

/-- The numeral `n`. -/
noncomputable def nm : ℕ → V
  | 0 => ∅
  | n + 1 => sc (nm n)

theorem nm_mem_of_lt : ∀ {a b : ℕ}, a < b → (nm a : V) ∈ (nm b : V)
  | a, 0, h => absurd h (Nat.not_lt_zero a)
  | a, b + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact mem_sc.mpr (Or.inr (nm_mem_of_lt h'))
    · exact self_mem_sc _

theorem nm_inj {a b : ℕ} (h : (nm a : V) = nm b) : a = b := by
  rcases Nat.lt_trichotomy a b with h' | h' | h'
  · have := nm_mem_of_lt (V := V) h'
    rw [h] at this
    exact absurd this (mem_irrefl _)
  · exact h'
  · have := nm_mem_of_lt (V := V) h'
    rw [h] at this
    exact absurd this (mem_irrefl _)

theorem nm_mem_om : ∀ n : ℕ, (nm n : V) ∈ (om : V)
  | 0 => empty_mem_om
  | n + 1 => sc_mem_om (nm_mem_om n)

theorem isNum_nm : ∀ n : ℕ, IsNum n (nm n : V)
  | 0 => fun w hw => absurd hw (by simp [nm])
  | n + 1 => ⟨nm n, self_mem_sc _, isNum_nm n, succR_iff_sc.mpr rfl⟩

theorem isNum_iff : ∀ (n : ℕ) (s : V), IsNum n s ↔ s = nm n
  | 0, s => ⟨fun h => mem_ext fun w => ⟨fun hw => (h w hw).elim, fun hw => absurd hw (by simp [nm])⟩,
      fun h => h ▸ isNum_nm 0⟩
  | n + 1, s => by
    constructor
    · rintro ⟨m, -, hm, hs⟩
      rw [succR_iff_sc.mp hs, (isNum_iff n m).mp hm]
      rfl
    · intro h
      exact h ▸ isNum_nm (n + 1)

/-- The set of the four tags. -/
noncomputable def Tg4 : V := nm 4

/-- The set of the addresses. -/
noncomputable def AU : V := AUset (Tg4 : V)

/-- The set of the codes with labels in `Lb`. -/
noncomputable def CdS (Lb : V) : V := ℘ (prodS (AU : V) Lb)

theorem tag_mem (j : Fin 4) : (nm j : V) ∈ (Tg4 : V) := nm_mem_of_lt j.2

/-- The tree with root label `β` and the subtrees `c 0, …, c 3`. -/
noncomputable def mk4 (Lb β : V) (c : Fin 4 → V) : V :=
  mkC (Tg4 : V) Lb β (nm 0) (nm 1) (nm 2) (nm 3) (c 0) (c 1) (c 2) (c 3)

theorem pr_mk4_child {Lb β : V} {c : Fin 4 → V} (hc : ∀ j, c j ∈ CdS Lb) (j : Fin 4) {w x : V}
    (hw : w ∈ (AU : V)) :
    Pr (mk4 Lb β c) (chA Tg4 (nm j) w) x ↔ Pr (c j) w x := by
  have hx : ∀ k : Fin 4, ∀ w x, Pr (c k) w x → x ∈ Lb := fun k w x h => by
    obtain ⟨w', -, x', hx', e⟩ := mem_prodS.mp (mem_power_iff.mp (hc k) _ (pr_iff.mp h))
    rw [(kp_inj e).2]; exact hx'
  have key : ∀ k : Fin 4, Pr (graft Tg4 Lb (nm k) (c k)) (chA Tg4 (nm j) w) x →
      Pr (c j) w x := by
    intro k h
    obtain ⟨-, -, w₂, hw₂, e, hpr⟩ := pr_graft.mp h
    obtain ⟨e1, rfl⟩ := chA_inj hw hw₂ e
    have : j = k := Fin.ext (nm_inj e1)
    subst this
    exact hpr
  have back : Pr (c j) w x → Pr (graft Tg4 Lb (nm j) (c j)) (chA Tg4 (nm j) w) x := fun h =>
    pr_graft.mpr ⟨chA_mem (tag_mem j) hw, hx j w x h, w, hw, rfl, h⟩
  rw [mk4, pr_mkC]
  constructor
  · rintro (⟨e, -⟩ | h | h | h | h)
    · exact absurd e chA_ne_empty
    · exact key 0 h
    · exact key 1 h
    · exact key 2 h
    · exact key 3 h
  · intro h
    have := back h
    fin_cases j
    · exact Or.inr (Or.inl this)
    · exact Or.inr (Or.inr (Or.inl this))
    · exact Or.inr (Or.inr (Or.inr (Or.inl this)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr this)))

theorem chC_mk4 {Lb β : V} {c : Fin 4 → V} (hc : ∀ j, c j ∈ CdS Lb) (j : Fin 4) :
    chC Tg4 Lb (nm j) (mk4 Lb β c) = c j := by
  refine mem_ext fun e => ⟨fun he => ?_, fun he => ?_⟩
  · obtain ⟨w, hw, x, hx, rfl⟩ := mem_prodS.mp (relB_sub _ _ _ _ he)
    obtain ⟨-, -, hpr⟩ := (pr_chC (tag_mem j)).mp (pr_iff.mpr he)
    exact pr_iff.mp ((pr_mk4_child hc j hw).mp hpr)
  · obtain ⟨w, hw, x, hx, rfl⟩ := mem_prodS.mp (mem_power_iff.mp (hc j) e he)
    exact pr_iff.mp ((pr_chC (tag_mem j)).mpr ⟨hw, hx,
      (pr_mk4_child hc j hw).mpr (pr_iff.mpr he)⟩)

theorem mk4_mem {Lb β : V} {c : Fin 4 → V} (hβ : β ∈ Lb) : mk4 Lb β c ∈ CdS Lb := mkC_mem hβ

theorem pr_mk4_root {Lb β γ : V} {c : Fin 4 → V} : Pr (mk4 Lb β c) ∅ γ ↔ γ = β := pr_mkC_root

/-- The relation "`c'` is the `j`-th subtree of the code `c`", as a set. -/
noncomputable def kidS (Lb : V) (j : Fin 4) : V :=
  relB (k := 4) isChildB (CdS Lb) (CdS Lb) ![nm j, ∅, (AU : V), Lb]

theorem pr_kidS {Lb c c' : V} {j : Fin 4} :
    Pr (kidS Lb j) c c' ↔ c ∈ CdS Lb ∧ c' = chC Tg4 Lb (nm j) c := by
  rw [kidS, pr_relB]
  constructor
  · rintro ⟨hc, hc', h⟩
    exact ⟨hc, (isChild_iff (tag_mem j) hc').mp h⟩
  · rintro ⟨hc, rfl⟩
    exact ⟨hc, chC_mem, (isChild_iff (tag_mem j) chC_mem).mpr rfl⟩

end model

end MH

end FFL.FirstOrder.SetTheory
