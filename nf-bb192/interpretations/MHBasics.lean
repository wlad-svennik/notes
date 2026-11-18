import Foundation.FirstOrder.SetTheory.BST.BST
import MInterpretsTST
import MHTheory

set_option autoImplicit false

/-!
# Tools inside a model of Mac Lane set theory

Working inside a model `V` of `𝗠`.

* `sepB`: the subset of a set given by a bounded condition, as a function.
* `kp`: Kuratowski pairs. `prodS`: products. `relB`: the set of pairs given by a bounded
  condition.
* `Ord`: ordinals (transitive sets of transitive sets). `ord_tri`: any two are comparable.
  `ord_least`: every set of ordinals with a member has a least member. `sc`: successor.
* `om`: ω, with `om_ind`.
-/

namespace FFL.FirstOrder.SetTheory

instance instBSTofM {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗠] :
    V↓[ℒₛₑₜ] ⊧* 𝗕𝗦𝗧 := models_of_subtheory (U := 𝗠) inferInstance

namespace BDef

variable {k : ℕ}

/-- Truth. -/
def tru : BDef (k := k) (fun _ _ _ ↦ True) := (BDef.fls.not).congr fun _ _ _ => by simp

end BDef

namespace MH

section

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-! ### Separation as a function -/

/-- `{z ∈ a | R (z, p)}` -/
noncomputable def sepB {k : ℕ} {R : MRel (k + 1)} (d : BDef R) (a : V) (p : Fin k → V) : V :=
  Classical.choose (d.sep a p)

theorem mem_sepB {k : ℕ} {R : MRel (k + 1)} (d : BDef R) (a : V) (p : Fin k → V) (z : V) :
    z ∈ sepB d a p ↔ z ∈ a ∧ R V (z :> p) := Classical.choose_spec (d.sep a p) z

theorem mem_irrefl (x : V) : x ∉ x := not_mem_self x

theorem mem_asymm {x y : V} (h : x ∈ y) : y ∉ x := by
  intro h'
  obtain ⟨z, hz, hmin⟩ := m_found ({x, y} : V) ⟨x, by simp⟩
  rcases (by simpa using hz : z = x ∨ z = y) with rfl | rfl
  · exact hmin y (by simp) h'
  · exact hmin x (by simp) h

/-! ### Pairs -/

/-- The Kuratowski pair. -/
noncomputable def kp (a b : V) : V := {{a}, {a, b}}

theorem isOp_kp (a b : V) : IsOp (kp a b) a b := by
  refine ⟨⟨{a}, by simp [kp], by simp [IsSing]⟩, ⟨{a, b}, by simp [kp], by simp [IsUp]⟩,
    fun z hz => ?_⟩
  rcases (by simpa [kp] using hz : z = {a} ∨ z = {a, b}) with rfl | rfl
  · exact Or.inl (by simp [IsSing])
  · exact Or.inr (by simp [IsUp])

theorem isOp_iff {p a b : V} : IsOp p a b ↔ p = kp a b := by
  constructor
  · rintro ⟨⟨s, hs, hsa⟩, ⟨d, hd, hdab⟩, hall⟩
    have es : s = {a} := mem_ext fun c => by
      simp only [mem_singleton_iff]
      exact ⟨hsa.2 c, fun e => e ▸ hsa.1⟩
    have ed : d = {a, b} := mem_ext fun c => by
      simp only [mem_insert, mem_singleton_iff]
      exact ⟨hdab.2.2 c, fun e => e.elim (fun e => e ▸ hdab.1) (fun e => e ▸ hdab.2.1)⟩
    refine mem_ext fun z => ?_
    simp only [kp, mem_insert, mem_singleton_iff]
    constructor
    · intro hz
      rcases hall z hz with h | h
      · left
        exact mem_ext fun c => by
          simp only [mem_singleton_iff]
          exact ⟨h.2 c, fun e => e ▸ h.1⟩
      · right
        exact mem_ext fun c => by
          simp only [mem_insert, mem_singleton_iff]
          exact ⟨h.2.2 c, fun e => e.elim (fun e => e ▸ h.1) (fun e => e ▸ h.2.1)⟩
    · rintro (rfl | rfl)
      · exact es ▸ hs
      · exact ed ▸ hd
  · rintro rfl
    exact isOp_kp a b

theorem kp_inj {a b a' b' : V} (h : kp a b = kp a' b') : a = a' ∧ b = b' :=
  op_inj (isOp_kp a b) (h ▸ isOp_kp a' b')

theorem pr_iff {r a b : V} : Pr r a b ↔ kp a b ∈ r :=
  ⟨fun ⟨p, hp, h⟩ => isOp_iff.mp h ▸ hp, fun h => ⟨kp a b, h, isOp_kp a b⟩⟩

theorem pr_fst_mem {p a b : V} (h : IsOp p a b) : ∃ u, u ∈ p ∧ a ∈ u :=
  let ⟨⟨s, hs, hsa⟩, _⟩ := h; ⟨s, hs, hsa.1⟩

theorem pr_snd_mem {p a b : V} (h : IsOp p a b) : ∃ u, u ∈ p ∧ b ∈ u :=
  let ⟨_, ⟨d, hd, hdab⟩, _⟩ := h; ⟨d, hd, hdab.2.1⟩

/-- The product of two sets. -/
noncomputable def prodS (a b : V) : V :=
  sepB (k := 2) ((BDef.bex 1 (BDef.bex 3 (isOpB.comp ![2, 1, 0])))) (℘ (℘ (a ∪ b))) ![a, b]

theorem mem_prodS {a b p : V} : p ∈ prodS a b ↔ ∃ x, x ∈ a ∧ ∃ y, y ∈ b ∧ p = kp x y := by
  constructor
  · intro h
    obtain ⟨-, x, hx, y, hy, hop⟩ := (mem_sepB _ _ _ p).mp h
    exact ⟨x, hx, y, hy, isOp_iff.mp hop⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine (mem_sepB _ _ _ _).mpr ⟨?_, x, hx, y, hy, isOp_kp x y⟩
    simp only [mem_power_iff, subset_def, kp, mem_insert, mem_singleton_iff, mem_union_iff]
    rintro z (rfl | rfl) w hw
    · rw [mem_singleton_iff.mp hw]; exact Or.inl hx
    · rcases (by simpa using hw : w = x ∨ w = y) with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hy

/-- The set of the pairs `⟨x, y⟩` with `x ∈ a`, `y ∈ b` and `R (x, y, p)`. -/
noncomputable def relB {k : ℕ} {R : MRel (k + 2)} (d : BDef R) (a b : V) (p : Fin k → V) : V :=
  sepB (k := k + 2) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
    (d.comp (fun i ↦ Fin.cases 1 (fun j ↦ Fin.cases 0
      (fun l ↦ l.succ.succ.succ.succ.succ) j) i))))) (prodS a b) (a :> b :> p)

theorem pr_relB {k : ℕ} {R : MRel (k + 2)} (d : BDef R) (a b : V) (p : Fin k → V) (x y : V) :
    Pr (relB d a b p) x y ↔ x ∈ a ∧ y ∈ b ∧ R V (x :> y :> p) := by
  have e : ∀ x' y' z : V, (fun i ↦ (y' :> x' :> z :> a :> b :> p)
      ((fun i ↦ Fin.cases 1 (fun j ↦ Fin.cases 0
        (fun l ↦ l.succ.succ.succ.succ.succ) j) i : Fin (k + 2) → Fin (k + 5)) i)) =
      (x' :> y' :> p) := by
    intro x' y' z
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => rfl
      | succ l => rfl
  rw [pr_iff]
  constructor
  · intro h
    obtain ⟨-, x', hx', y', hy', hop, hR⟩ := (mem_sepB _ _ _ _).mp h
    obtain ⟨rfl, rfl⟩ := op_inj (isOp_kp x y) hop
    refine ⟨hx', hy', ?_⟩
    have hR' : R V (fun i ↦ (y :> x :> kp x y :> a :> b :> p)
      ((fun i ↦ Fin.cases 1 (fun j ↦ Fin.cases 0
        (fun l ↦ l.succ.succ.succ.succ.succ) j) i : Fin (k + 2) → Fin (k + 5)) i)) := hR
    rw [e] at hR'
    exact hR'
  · rintro ⟨hx, hy, hR⟩
    refine (mem_sepB _ _ _ _).mpr ⟨mem_prodS.mpr ⟨x, hx, y, hy, rfl⟩, x, hx, y, hy,
      isOp_kp x y, ?_⟩
    show R V (fun i ↦ (y :> x :> kp x y :> a :> b :> p)
      ((fun i ↦ Fin.cases 1 (fun j ↦ Fin.cases 0
        (fun l ↦ l.succ.succ.succ.succ.succ) j) i : Fin (k + 2) → Fin (k + 5)) i))
    rw [e]
    exact hR

/-! ### Ordinals -/

/-- An ordinal: a transitive set of transitive sets. -/
def Ord (γ : V) : Prop := Tr γ ∧ ∀ β, β ∈ γ → Tr β

omit [Nonempty V] hV in
theorem ord_mem {γ β : V} (h : Ord γ) (hβ : β ∈ γ) : Ord β :=
  ⟨h.2 β hβ, fun α hα => h.2 α (h.1 β hβ α hα)⟩

/-- Successor. -/
noncomputable def sc (γ : V) : V := insert γ γ

theorem mem_sc {γ z : V} : z ∈ sc γ ↔ z = γ ∨ z ∈ γ := by simp [sc]

theorem self_mem_sc (γ : V) : γ ∈ sc γ := mem_sc.mpr (Or.inl rfl)

theorem ord_sc {γ : V} (h : Ord γ) : Ord (sc γ) := by
  refine ⟨fun y hy z hz => ?_, fun β hβ => ?_⟩
  · rcases mem_sc.mp hy with rfl | hy
    · exact mem_sc.mpr (Or.inr hz)
    · exact mem_sc.mpr (Or.inr (h.1 y hy z hz))
  · rcases mem_sc.mp hβ with rfl | hβ
    · exact h.1
    · exact h.2 β hβ

theorem ord_empty : Ord (∅ : V) := ⟨fun y hy => absurd hy (by simp), fun β hβ => absurd hβ (by simp)⟩

end

def ordB : BDef (k := 1) (fun V _ v ↦ Ord (v 0)) :=
  ((trB.comp ![0]).and (BDef.ball 0 (trB.comp ![0]))).congr fun _ _ _ => Iff.rfl

section

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- For ordinals: if `α ⊆ β` and `α ≠ β` then `α ∈ β`. -/
theorem ord_mem_of_ssub {α β : V} (hα : Ord α) (hβ : Ord β) (hsub : ∀ z, z ∈ α → z ∈ β)
    (hne : α ≠ β) : α ∈ β := by
  -- induction inside `sc β`
  by_contra hcon
  let Z : V := sepB (k := 1) (BDef.bex 1 ((ordB.comp ![0]).and
    ((BDef.ball 0 (BDef.mem 0 2)).and (((BDef.eq 0 1).not).and (BDef.mem 0 1).not))))
    (sc β) ![℘ β]
  have hZ : ∀ b, b ∈ Z ↔ b ∈ sc β ∧ ∃ a, a ∈ ℘ β ∧ Ord a ∧ (∀ z, z ∈ a → z ∈ b) ∧ ¬a = b ∧
      ¬a ∈ b := fun b => mem_sepB _ _ _ b
  have hβZ : β ∈ Z := (hZ β).mpr ⟨self_mem_sc β, α, mem_power_iff.mpr hsub, hα, hsub, hne, hcon⟩
  obtain ⟨b, hb, hmin⟩ := m_found Z ⟨β, hβZ⟩
  obtain ⟨hbβ, a, -, ha, hab, hne', hnab⟩ := (hZ b).mp hb
  have hbO : Ord b := by
    rcases mem_sc.mp hbβ with rfl | h
    · exact hβ
    · exact ord_mem hβ h
  have hbsub : ∀ z, z ∈ b → z ∈ β := fun z hz => by
    rcases mem_sc.mp hbβ with rfl | h
    · exact hz
    · exact hβ.1 b h z hz
  -- a least member of `b \ a`
  let D : V := sepB (k := 1) (BDef.mem 0 1).not b ![a]
  have hD : ∀ z, z ∈ D ↔ z ∈ b ∧ ¬z ∈ a := fun z => mem_sepB _ _ _ z
  have hDne : ∃ z, z ∈ D := by
    by_contra h
    exact hne' (mem_ext fun z => ⟨hab z, fun hz => by
      by_contra hza
      exact h ⟨z, (hD z).mpr ⟨hz, hza⟩⟩⟩)
  obtain ⟨g, hg, hgmin⟩ := m_found D hDne
  obtain ⟨hgb, hga⟩ := (hD g).mp hg
  have hgO : Ord g := ord_mem hbO hgb
  have hg_sub : ∀ z, z ∈ g → z ∈ a := fun z hz => by
    by_contra hza
    exact hgmin z ((hD z).mpr ⟨hbO.1 g hgb z hz, hza⟩) hz
  have ha_sub : ∀ z, z ∈ a → z ∈ g := by
    by_contra hnot
    let E : V := sepB (k := 1) (BDef.mem 0 1).not a ![g]
    have hE : ∀ z, z ∈ E ↔ z ∈ a ∧ ¬z ∈ g := fun z => mem_sepB _ _ _ z
    have hEne : ∃ z, z ∈ E := by
      by_contra h
      exact hnot fun z hz => by
        by_contra hzg
        exact h ⟨z, (hE z).mpr ⟨hz, hzg⟩⟩
    obtain ⟨d, hd, hdmin⟩ := m_found E hEne
    obtain ⟨hda, hdg⟩ := (hE d).mp hd
    have hdO : Ord d := ord_mem ha hda
    have hd_sub : ∀ z, z ∈ d → z ∈ g := fun z hz => by
      by_contra hzg
      exact hdmin z ((hE z).mpr ⟨ha.1 d hda z hz, hzg⟩) hz
    have hdne : d ≠ g := fun e => hga (e ▸ hda)
    -- `g ∈ b`, so `g ∉ Z`
    have hgZ : ¬g ∈ Z := fun h => hmin g h hgb
    exact hgZ ((hZ g).mpr ⟨mem_sc.mpr (Or.inr (hbsub g hgb)), d,
      mem_power_iff.mpr (fun z hz => hbsub z (hbO.1 g hgb z (hd_sub z hz))), hdO, hd_sub, hdne, hdg⟩)
  have e : a = g := mem_ext fun z => ⟨ha_sub z, hg_sub z⟩
  exact hnab (e ▸ hgb)

/-- **Any two ordinals are comparable.** -/
theorem ord_tri {α β : V} (hα : Ord α) (hβ : Ord β) : α ∈ β ∨ α = β ∨ β ∈ α := by
  let G : V := sepB (k := 1) (BDef.mem 0 1) α ![β]
  have hG : ∀ z, z ∈ G ↔ z ∈ α ∧ z ∈ β := fun z => mem_sepB _ _ _ z
  have hGO : Ord G := by
    refine ⟨fun y hy z hz => ?_, fun y hy => hα.2 y ((hG y).mp hy).1⟩
    exact (hG z).mpr ⟨hα.1 y ((hG y).mp hy).1 z hz, hβ.1 y ((hG y).mp hy).2 z hz⟩
  by_cases h1 : G = α
  · by_cases h2 : α = β
    · exact Or.inr (Or.inl h2)
    · exact Or.inl (ord_mem_of_ssub hα hβ (fun z hz => ((hG z).mp (h1 ▸ hz)).2) h2)
  · by_cases h2 : G = β
    · by_cases h3 : β = α
      · exact Or.inr (Or.inl h3.symm)
      · exact Or.inr (Or.inr (ord_mem_of_ssub hβ hα (fun z hz => ((hG z).mp (h2 ▸ hz)).1) h3))
    · have hGα := ord_mem_of_ssub hGO hα (fun z hz => ((hG z).mp hz).1) h1
      have hGβ := ord_mem_of_ssub hGO hβ (fun z hz => ((hG z).mp hz).2) h2
      exact absurd ((hG G).mpr ⟨hGα, hGβ⟩) (mem_irrefl G)

/-- **Every set of ordinals with a member has a least member.** -/
theorem ord_least (Z : V) (hZ : ∀ z, z ∈ Z → Ord z) (hne : ∃ z, z ∈ Z) :
    ∃ z, z ∈ Z ∧ ∀ w, w ∈ Z → z = w ∨ z ∈ w := by
  obtain ⟨z, hz, hmin⟩ := m_found Z hne
  refine ⟨z, hz, fun w hw => ?_⟩
  rcases ord_tri (hZ z hz) (hZ w hw) with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd h (hmin w hw)

theorem ord_le_iff {α β : V} (hα : Ord α) (hβ : Ord β) :
    (∀ z, z ∈ α → z ∈ β) ↔ α = β ∨ α ∈ β := by
  constructor
  · intro h
    by_cases e : α = β
    · exact Or.inl e
    · exact Or.inr (ord_mem_of_ssub hα hβ h e)
  · rintro (rfl | h) z hz
    · exact hz
    · exact hβ.1 α h z hz

theorem ord_sc_le {α β : V} (hα : Ord α) (hβ : Ord β) (h : α ∈ β) : sc α = β ∨ sc α ∈ β :=
  (ord_le_iff (ord_sc hα) hβ).mp fun z hz => by
    rcases mem_sc.mp hz with rfl | hz
    · exact h
    · exact hβ.1 α h z hz

/-- A limit ordinal: it has a member, and the successor of every member is a member. -/
def Lim (lam : V) : Prop := Ord lam ∧ (∃ z, z ∈ lam) ∧ ∀ β, β ∈ lam → sc β ∈ lam

/-! ### ω -/

/-- ω -/
noncomputable def om : V := lvl 0

theorem succR_iff_sc {y x : V} : SuccR y x ↔ y = sc x :=
  ⟨fun h => mem_ext fun z => ((succR_iff.mp h) z).trans mem_sc.symm,
    fun h => succR_iff.mpr fun z => h ▸ mem_sc⟩

theorem empty_mem_om : (∅ : V) ∈ (om : V) := by
  obtain ⟨⟨e, he, hee⟩, -⟩ := indR_omega (V := V)
  have : e = ∅ := mem_ext fun z => ⟨fun hz => absurd hz (hee z), fun hz => absurd hz (by simp)⟩
  exact this ▸ he

theorem sc_mem_om {n : V} (hn : n ∈ (om : V)) : sc n ∈ (om : V) := by
  obtain ⟨y, hy, hyn⟩ := (indR_omega (V := V)).2 n hn
  exact succR_iff_sc.mp hyn ▸ hy

/-- **Induction on ω**, for properties with a bounded definition. -/
theorem om_ind {k : ℕ} {R : MRel (k + 1)} (d : BDef R) (p : Fin k → V)
    (h0 : R V ((∅ : V) :> p)) (hs : ∀ n, n ∈ (om : V) → R V (n :> p) → R V (sc n :> p)) :
    ∀ n, n ∈ (om : V) → R V (n :> p) := by
  refine nat_induction d p (fun e _ he => ?_) (fun x hx hR y _ hy => ?_)
  · have : e = ∅ := mem_ext fun z => ⟨fun hz => absurd hz (he z), fun hz => absurd hz (by simp)⟩
    exact this ▸ h0
  · exact succR_iff_sc.mp hy ▸ hs x hx hR

theorem om_tr : Tr (om : V) := by
  have := om_ind (BDef.ball 0 (BDef.mem 0 2)) ![(om : V)]
    (fun m hm => absurd hm (by simp))
    (fun n hn ih m hm => by
      rcases mem_sc.mp hm with rfl | hm
      · exact hn
      · exact ih m hm)
  exact fun n hn m hm => this n hn m hm

theorem ord_om : Ord (om : V) := ⟨om_tr, fun n hn y hy z hz => nat_trans n hn y hy z hz⟩

theorem lim_om : Lim (om : V) := ⟨ord_om, ⟨∅, empty_mem_om⟩, fun _ h => sc_mem_om h⟩

theorem om_cases {n : V} (hn : n ∈ (om : V)) : n = ∅ ∨ ∃ m, m ∈ (om : V) ∧ n = sc m := by
  have := om_ind (k := 1) ((BDef.ball 0 BDef.fls).or (BDef.bex 1 (succB.comp ![1, 0])))
    ![(om : V)] (Or.inl fun z hz => absurd hz (by simp))
    (fun n hn _ => Or.inr ⟨n, hn, succR_iff_sc.mpr rfl⟩) n hn
  rcases this with h | ⟨m, hm, h⟩
  · exact Or.inl (mem_ext fun z => ⟨fun hz => (h z hz).elim, fun hz => absurd hz (by simp)⟩)
  · exact Or.inr ⟨m, hm, succR_iff_sc.mp h⟩

end

end MH

end FFL.FirstOrder.SetTheory
