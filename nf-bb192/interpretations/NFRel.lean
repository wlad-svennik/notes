import NFStrat

set_option autoImplicit false

/-!
# Well-founded pointed graphs in a model of `𝗡𝗙`

A *graph* is any set `r`; its edges are the Kuratowski pairs that belong to it, and `Rl r a b`
says that there is an edge from `a` to `b`. A pointed graph `(r, t)` is read as a picture of a
set: the node `t` stands for a set whose members are the sets pictured by `(r, a)` for the
edges `a → t`. Two pointed graphs picture the same set when they are bisimilar (`Bis`).

* `IsType x r t`: `x` is the set of (codes of) the well-founded pointed graphs bisimilar to
  `(r, t)`. `InZ x`: `x` is the type of some well-founded pointed graph.
* `EE x y`: the membership relation on types.
* `ee_iff`: the members of the type of `(r, t)` are the types of `(r, a)` for `a → t`.
* `ee_ext`: types with the same members are equal. `ee_wf`: every set that contains a type
  has a type with no member in the set.

Every notion comes with an `SDef`, so that it can be used in comprehension.
-/

namespace FFL.FirstOrder.SetTheory

namespace Hin

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `u = {a}` -/
def IsSing (u a : V) : Prop := ∀ c, c ∈ u ↔ c = a

/-- `u = {a, b}` -/
def IsUp (u a b : V) : Prop := ∀ c, c ∈ u ↔ c = a ∨ c = b

/-- `p = ⟨a, b⟩`, the Kuratowski pair. -/
def IsOp (p a b : V) : Prop := ∀ z, z ∈ p ↔ IsSing z a ∨ IsUp z a b

/-- The graph `r` has an edge from `a` to `b`. -/
def Rl (r a b : V) : Prop := ∃ p, p ∈ r ∧ IsOp p a b

/-- Every set with a member has a member with no predecessor in the set. -/
def WF (r : V) : Prop := ∀ X : V, (∃ c, c ∈ X) → ∃ c, c ∈ X ∧ ∀ b, b ∈ X → ¬ Rl r b c

/-- `B` is a bisimulation between the graphs `r` and `s`. -/
def IsBis (B r s : V) : Prop := ∀ a a', Rl B a a' →
  (∀ b, Rl r b a → ∃ b', Rl s b' a' ∧ Rl B b b') ∧ (∀ b', Rl s b' a' → ∃ b, Rl r b a ∧ Rl B b b')

/-- The pointed graphs `(r, t)` and `(s, u)` are bisimilar. -/
def Bis (r t s u : V) : Prop := ∃ B, IsBis B r s ∧ Rl B t u

/-- `k = {{{t}}}` -/
def IsSing3 (k t : V) : Prop := ∃ k₁ k₂, IsSing k₁ t ∧ IsSing k₂ k₁ ∧ IsSing k k₂

/-- `q` is the code `⟨r, {{{t}}}⟩` of the pointed graph `(r, t)`. -/
def IsPG (q r t : V) : Prop := ∃ k, IsSing3 k t ∧ IsOp q r k

/-- `x` is the type of the pointed graph `(r, t)`: the set of the codes of the well-founded
pointed graphs bisimilar to it. -/
def IsType (x r t : V) : Prop := ∀ q, q ∈ x ↔ ∃ s u, IsPG q s u ∧ WF s ∧ Bis s u r t

/-- `x` is the type of a well-founded pointed graph. -/
def InZ (x : V) : Prop := ∃ r t, WF r ∧ IsType x r t

/-- Membership between types. -/
def EE (x y : V) : Prop := InZ x ∧ InZ y ∧
  ∃ q q' s t a, q ∈ y ∧ IsPG q s t ∧ Rl s a t ∧ IsPG q' s a ∧ q' ∈ x

/-- `g` is the graph of `EE`. -/
def IsEg (g : V) : Prop := ∀ p, p ∈ g ↔ ∃ u v, IsOp p u v ∧ EE u v

/-- `y` is the type of the graph of `EE` pointed at `x`. -/
def IsTheta (y x : V) : Prop := ∃ g, IsEg g ∧ IsType y g x

end defs

/-! ### Stratified definitions -/

section sdefs

open SDef

def isSingD : SDef ![1, 0] (fun _ _ v ↦ IsSing (v 0) (v 1)) :=
  (SDef.all 0 ((SDef.mem 0 1).iff (SDef.eq 0 2))).congr fun _ _ _ => Iff.rfl

def isUpD : SDef ![1, 0, 0] (fun _ _ v ↦ IsUp (v 0) (v 1) (v 2)) :=
  (SDef.all 0 ((SDef.mem 0 1).iff ((SDef.eq 0 2).or (SDef.eq 0 3)))).congr fun _ _ _ => Iff.rfl

def isOpD : SDef ![2, 0, 0] (fun _ _ v ↦ IsOp (v 0) (v 1) (v 2)) :=
  (SDef.all 1 ((SDef.mem 0 1).iff
    ((isSingD.comp ![0, 2] 0).or (isUpD.comp ![0, 2, 3] 0)))).congr fun _ _ _ => Iff.rfl

def rlD : SDef ![3, 0, 0] (fun _ _ v ↦ Rl (v 0) (v 1) (v 2)) :=
  (SDef.ex 2 ((SDef.mem 0 1).and (isOpD.comp ![0, 2, 3] 0))).congr fun _ _ _ => Iff.rfl

def wfD : SDef ![3] (fun _ _ v ↦ WF (v 0)) :=
  (SDef.all 1 ((SDef.ex 0 (SDef.mem 0 1)).imp
    (SDef.ex 0 ((SDef.mem 0 1).and
      (SDef.all 0 ((SDef.mem 0 2).imp (rlD.comp ![3, 0, 1] 0).not)))))).congr
    fun _ _ _ => Iff.rfl

def isBisD : SDef ![3, 3, 3] (fun _ _ v ↦ IsBis (v 0) (v 1) (v 2)) :=
  (SDef.all 0 (SDef.all 0 ((rlD.comp ![2, 1, 0] 0).imp
    ((SDef.all 0 ((rlD.comp ![4, 0, 2] 0).imp
        (SDef.ex 0 ((rlD.comp ![6, 0, 2] 0).and (rlD.comp ![4, 1, 0] 0))))).and
      (SDef.all 0 ((rlD.comp ![5, 0, 1] 0).imp
        (SDef.ex 0 ((rlD.comp ![5, 0, 3] 0).and (rlD.comp ![4, 0, 1] 0))))))))).congr
    fun _ _ _ => Iff.rfl

def bisD : SDef ![3, 0, 3, 0] (fun _ _ v ↦ Bis (v 0) (v 1) (v 2) (v 3)) :=
  (SDef.ex 3 ((isBisD.comp ![0, 1, 3] 0).and (rlD.comp ![0, 2, 4] 0))).congr
    fun _ _ _ => Iff.rfl

def isSing3D : SDef ![3, 0] (fun _ _ v ↦ IsSing3 (v 0) (v 1)) :=
  (SDef.ex 1 (SDef.ex 2 ((isSingD.comp ![1, 3] 0).and
    ((isSingD.comp ![0, 1] 1).and (isSingD.comp ![2, 0] 2))))).congr fun _ _ _ => Iff.rfl

def isPGD : SDef ![5, 3, 0] (fun _ _ v ↦ IsPG (v 0) (v 1) (v 2)) :=
  (SDef.ex 3 ((isSing3D.comp ![0, 3] 0).and (isOpD.comp ![1, 2, 0] 3))).congr
    fun _ _ _ => Iff.rfl

def isTypeD : SDef ![6, 3, 0] (fun _ _ v ↦ IsType (v 0) (v 1) (v 2)) :=
  (SDef.all 5 ((SDef.mem 0 1).iff (SDef.ex 3 (SDef.ex 0
    ((isPGD.comp ![2, 1, 0] 0).and ((wfD.comp ![1] 0).and (bisD.comp ![1, 0, 4, 5] 0))))))).congr
    fun _ _ _ => Iff.rfl

def inZD : SDef ![6] (fun _ _ v ↦ InZ (v 0)) :=
  (SDef.ex 3 (SDef.ex 0 ((wfD.comp ![1] 0).and (isTypeD.comp ![2, 1, 0] 0)))).congr
    fun _ _ _ => Iff.rfl

def eeD : SDef ![6, 6] (fun _ _ v ↦ EE (v 0) (v 1)) :=
  ((inZD.comp ![0] 0).and ((inZD.comp ![1] 0).and
    (SDef.ex 5 (SDef.ex 5 (SDef.ex 3 (SDef.ex 0 (SDef.ex 0
      ((SDef.mem 4 6).and ((isPGD.comp ![4, 2, 1] 0).and ((rlD.comp ![2, 0, 1] 0).and
        ((isPGD.comp ![3, 2, 0] 0).and (SDef.mem 3 5)))))))))))).congr fun _ _ _ => Iff.rfl

def isEgD : SDef ![9] (fun _ _ v ↦ IsEg (v 0)) :=
  (SDef.all 8 ((SDef.mem 0 1).iff (SDef.ex 6 (SDef.ex 6
    ((isOpD.comp ![2, 1, 0] 6).and (eeD.comp ![1, 0] 0)))))).congr fun _ _ _ => Iff.rfl

def isThetaD : SDef ![12, 6] (fun _ _ v ↦ IsTheta (v 0) (v 1)) :=
  (SDef.ex 9 ((isEgD.comp ![0] 0).and (isTypeD.comp ![1, 0, 2] 6))).congr fun _ _ _ => Iff.rfl

end sdefs

/-! ### Singletons and pairs in a model of `𝗡𝗙` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

theorem exists_sing (a : V) : ∃ u, IsSing u a :=
  (SDef.eq (τ := ![0, 0]) 0 1).comprehension ![a]

theorem exists_up (a b : V) : ∃ u, IsUp u a b :=
  ((SDef.eq (τ := ![0, 0, 0]) 0 1).or (SDef.eq 0 2)).comprehension ![a, b]

theorem exists_op (a b : V) : ∃ p, IsOp p a b :=
  ((isSingD.comp (τ' := ![1, 0, 0]) ![0, 1] 0).or (isUpD.comp ![0, 1, 2] 0)).comprehension ![a, b]

omit [Nonempty V] hT in
theorem mem_sing {u a : V} (h : IsSing u a) : a ∈ u := (h a).mpr rfl

omit [Nonempty V] hT in
theorem sing_inj {u a b : V} (h : IsSing u a) (h' : IsSing u b) : a = b :=
  (h' a).mp (mem_sing h)

theorem sing_unique {u u' a : V} (h : IsSing u a) (h' : IsSing u' a) : u = u' :=
  nf_ext fun z => (h z).trans (h' z).symm

theorem up_unique {u u' a b : V} (h : IsUp u a b) (h' : IsUp u' a b) : u = u' :=
  nf_ext fun z => (h z).trans (h' z).symm

theorem op_unique {p p' a b : V} (h : IsOp p a b) (h' : IsOp p' a b) : p = p' :=
  nf_ext fun z => (h z).trans (h' z).symm

theorem op_inj {p a b a' b' : V} (h : IsOp p a b) (h' : IsOp p a' b') : a = a' ∧ b = b' := by
  obtain ⟨sa, hsa⟩ := exists_sing a
  obtain ⟨u, hu⟩ := exists_up a b
  obtain ⟨u', hu'⟩ := exists_up a' b'
  have ha : a = a' := by
    rcases (h' sa).mp ((h sa).mpr (Or.inl hsa)) with h1 | h1
    · exact sing_inj hsa h1
    · exact ((hsa a').mp ((h1 a').mpr (Or.inl rfl))).symm
  subst ha
  refine ⟨rfl, ?_⟩
  have hb : b = a ∨ b = b' := by
    rcases (h' u).mp ((h u).mpr (Or.inr hu)) with h1 | h1
    · exact Or.inl ((h1 b).mp ((hu b).mpr (Or.inr rfl)))
    · exact (h1 b).mp ((hu b).mpr (Or.inr rfl))
  have hb' : b' = a ∨ b' = b := by
    rcases (h u').mp ((h' u').mpr (Or.inr hu')) with h1 | h1
    · exact Or.inl ((h1 b').mp ((hu' b').mpr (Or.inr rfl)))
    · exact (h1 b').mp ((hu' b').mpr (Or.inr rfl))
  rcases hb with hb | hb
  · rcases hb' with hb' | hb'
    · rw [hb, hb']
    · exact hb'.symm
  · exact hb

/-- An edge in a graph given by the pairs satisfying a condition. -/
theorem rl_of_spec {r : V} {P : V → V → Prop}
    (hr : ∀ q, q ∈ r ↔ ∃ a b, IsOp q a b ∧ P a b) (a b : V) : Rl r a b ↔ P a b := by
  constructor
  · rintro ⟨q, hq, hop⟩
    obtain ⟨a', b', hop', hP⟩ := (hr q).mp hq
    obtain ⟨rfl, rfl⟩ := op_inj hop hop'
    exact hP
  · intro hP
    obtain ⟨q, hq⟩ := exists_op a b
    exact ⟨q, (hr q).mpr ⟨a, b, hq, hP⟩, hq⟩

/-- **Relations by comprehension.** If `R (a, b, p)` has a stratified definition in which `a`
and `b` have the same type `n₀`, there is a graph whose edges are the pairs `a → b` with
`R (a, b, p)`. -/
theorem exists_rel {k : ℕ} {τ : Fin k → ℕ} (n₀ : ℕ) {R : URel (k + 2)}
    (d : SDef (n₀ :> n₀ :> τ) R) (p : Fin k → V) :
    ∃ r : V, ∀ a b, Rl r a b ↔ R V (a :> b :> p) := by
  let f : Fin (k + 2) → Fin (k + 3) :=
    fun i ↦ Fin.cases 1 (fun j ↦ Fin.cases 0 (fun l ↦ l.succ.succ.succ) j) i
  have hf : ∀ i, (n₀ :> n₀ :> (n₀ + 2) :> τ) (f i) = (n₀ :> n₀ :> τ) i + 0 := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => rfl
      | succ l => rfl
  have hg : ∀ i, (n₀ :> n₀ :> (n₀ + 2) :> τ) (![2, 1, 0] i) = ![2, 0, 0] i + n₀ := by
    intro i; fin_cases i
    · show n₀ + 2 = 2 + n₀; omega
    · show n₀ = 0 + n₀; omega
    · show n₀ = 0 + n₀; omega
  obtain ⟨r, hr⟩ := (SDef.ex n₀ (SDef.ex n₀
    ((isOpD.comp (τ' := n₀ :> n₀ :> (n₀ + 2) :> τ) ![2, 1, 0] n₀ hg).and
      (d.comp f 0 hf)))).comprehension p
  refine ⟨r, rl_of_spec (P := fun a b ↦ R V (a :> b :> p)) fun q => (hr q).trans ?_⟩
  refine exists_congr fun a => exists_congr fun b => and_congr Iff.rfl ?_
  have e : (fun i ↦ (b :> a :> q :> p) (f i)) = (a :> b :> p) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => rfl
      | succ l => rfl
  show R V (fun i ↦ (b :> a :> q :> p) (f i)) ↔ _
  rw [e]

/-! ### Bisimilarity is an equivalence relation -/

theorem bis_refl (r t : V) : Bis r t r t := by
  obtain ⟨B, hB⟩ := exists_rel 0 (SDef.eq (τ := ![0, 0]) 0 1) (![] : Fin 0 → V)
  have hB' : ∀ a b, Rl B a b ↔ a = b := hB
  refine ⟨B, fun a a' h => ?_, (hB' t t).mpr rfl⟩
  obtain rfl := (hB' a a').mp h
  exact ⟨fun b hb => ⟨b, hb, (hB' b b).mpr rfl⟩, fun b hb => ⟨b, hb, (hB' b b).mpr rfl⟩⟩

theorem bis_symm {r t s u : V} (h : Bis r t s u) : Bis s u r t := by
  obtain ⟨B, hB, ht⟩ := h
  obtain ⟨B', hB'⟩ := exists_rel 0 (rlD.comp (τ' := ![0, 0, 3]) ![2, 1, 0] 0) ![B]
  have hB'' : ∀ a b, Rl B' a b ↔ Rl B b a := hB'
  refine ⟨B', fun a' a h => ?_, (hB'' u t).mpr ht⟩
  have h1 := hB a a' ((hB'' a' a).mp h)
  exact ⟨fun b' hb' => let ⟨b, hb, hbb⟩ := h1.2 b' hb'; ⟨b, hb, (hB'' b' b).mpr hbb⟩,
    fun b hb => let ⟨b', hb', hbb⟩ := h1.1 b hb; ⟨b', hb', (hB'' b' b).mpr hbb⟩⟩

theorem bis_trans {r t s u r' t' : V} (h : Bis r t s u) (h' : Bis s u r' t') :
    Bis r t r' t' := by
  obtain ⟨B, hB, ht⟩ := h
  obtain ⟨B', hB', hu⟩ := h'
  obtain ⟨C, hC⟩ := exists_rel 0 (SDef.ex (τ := ![0, 0, 3, 3]) 0
    ((rlD.comp ![3, 1, 0] 0).and (rlD.comp ![4, 0, 2] 0))) ![B, B']
  have hC' : ∀ a c, Rl C a c ↔ ∃ b, Rl B a b ∧ Rl B' b c := hC
  refine ⟨C, fun a c h => ?_, (hC' t t').mpr ⟨u, ht, hu⟩⟩
  obtain ⟨b, hab, hbc⟩ := (hC' a c).mp h
  constructor
  · intro a₁ ha₁
    obtain ⟨b₁, hb₁, h1⟩ := (hB a b hab).1 a₁ ha₁
    obtain ⟨c₁, hc₁, h2⟩ := (hB' b c hbc).1 b₁ hb₁
    exact ⟨c₁, hc₁, (hC' a₁ c₁).mpr ⟨b₁, h1, h2⟩⟩
  · intro c₁ hc₁
    obtain ⟨b₁, hb₁, h2⟩ := (hB' b c hbc).2 c₁ hc₁
    obtain ⟨a₁, ha₁, h1⟩ := (hB a b hab).2 b₁ hb₁
    exact ⟨a₁, ha₁, (hC' a₁ c₁).mpr ⟨b₁, h1, h2⟩⟩

omit [Nonempty V] hT in
/-- A bisimulation restricts to the predecessors. -/
theorem bis_pred {r t s u a : V} (h : Bis r t s u) (ha : Rl r a t) :
    ∃ a', Rl s a' u ∧ Bis r a s a' := by
  obtain ⟨B, hB, ht⟩ := h
  obtain ⟨a', ha', h1⟩ := (hB t u ht).1 a ha
  exact ⟨a', ha', B, hB, h1⟩

/-! ### Codes of pointed graphs, and types -/

theorem exists_sing3 (t : V) : ∃ k, IsSing3 k t := by
  obtain ⟨k₁, h₁⟩ := exists_sing t
  obtain ⟨k₂, h₂⟩ := exists_sing k₁
  obtain ⟨k, h⟩ := exists_sing k₂
  exact ⟨k, k₁, k₂, h₁, h₂, h⟩

theorem sing3_unique {k k' t : V} (h : IsSing3 k t) (h' : IsSing3 k' t) : k = k' := by
  obtain ⟨k₁, k₂, h₁, h₂, h₃⟩ := h
  obtain ⟨k₁', k₂', h₁', h₂', h₃'⟩ := h'
  obtain rfl := sing_unique h₁ h₁'
  obtain rfl := sing_unique h₂ h₂'
  exact sing_unique h₃ h₃'

omit [Nonempty V] hT in
theorem sing3_inj {k t t' : V} (h : IsSing3 k t) (h' : IsSing3 k t') : t = t' := by
  obtain ⟨k₁, k₂, h₁, h₂, h₃⟩ := h
  obtain ⟨k₁', k₂', h₁', h₂', h₃'⟩ := h'
  obtain rfl := sing_inj h₃ h₃'
  obtain rfl := sing_inj h₂ h₂'
  exact sing_inj h₁ h₁'

theorem exists_pg (r t : V) : ∃ q, IsPG q r t := by
  obtain ⟨k, hk⟩ := exists_sing3 t
  obtain ⟨q, hq⟩ := exists_op r k
  exact ⟨q, k, hk, hq⟩

theorem pg_inj {q r t r' t' : V} (h : IsPG q r t) (h' : IsPG q r' t') : r = r' ∧ t = t' := by
  obtain ⟨k, hk, hq⟩ := h
  obtain ⟨k', hk', hq'⟩ := h'
  obtain ⟨rfl, rfl⟩ := op_inj hq hq'
  exact ⟨rfl, sing3_inj hk hk'⟩

theorem exists_type (r t : V) : ∃ x, IsType x r t :=
  (SDef.ex (τ := ![5, 3, 0]) 3 (SDef.ex 0 ((isPGD.comp ![2, 1, 0] 0).and
    ((wfD.comp ![1] 0).and (bisD.comp ![1, 0, 3, 4] 0))))).comprehension ![r, t]

theorem mem_type_iff {x r t q s u : V} (hx : IsType x r t) (hq : IsPG q s u) :
    q ∈ x ↔ WF s ∧ Bis s u r t := by
  constructor
  · intro h
    obtain ⟨s', u', hq', hw, hb⟩ := (hx q).mp h
    obtain ⟨rfl, rfl⟩ := pg_inj hq hq'
    exact ⟨hw, hb⟩
  · exact fun h => (hx q).mpr ⟨s, u, hq, h.1, h.2⟩

theorem type_unique {x x' r t : V} (h : IsType x r t) (h' : IsType x' r t) : x = x' :=
  nf_ext fun q => (h q).trans (h' q).symm

theorem isType_of_bis {x r t s u : V} (hx : IsType x r t) (h : Bis r t s u) : IsType x s u :=
  fun q => (hx q).trans ⟨fun ⟨s', u', hq, hw, hb⟩ => ⟨s', u', hq, hw, bis_trans hb h⟩,
    fun ⟨s', u', hq, hw, hb⟩ => ⟨s', u', hq, hw, bis_trans hb (bis_symm h)⟩⟩

theorem bis_of_type {x r t s u : V} (hr : WF r) (hx : IsType x r t) (hy : IsType x s u) :
    Bis r t s u := by
  obtain ⟨q, hq⟩ := exists_pg r t
  exact ((mem_type_iff hy hq).mp ((mem_type_iff hx hq).mpr ⟨hr, bis_refl r t⟩)).2

theorem inZ_nonempty {x : V} (h : InZ x) : ∃ q, q ∈ x := by
  obtain ⟨r, t, hr, hx⟩ := h
  obtain ⟨q, hq⟩ := exists_pg r t
  exact ⟨q, (mem_type_iff hx hq).mpr ⟨hr, bis_refl r t⟩⟩

/-- **The members of a type.** The members of the type of `(r, t)` are the types of `(r, a)`
for the edges `a → t`. -/
theorem ee_iff {y r t v : V} (hr : WF r) (hy : IsType y r t) :
    EE v y ↔ ∃ a, Rl r a t ∧ IsType v r a := by
  constructor
  · rintro ⟨⟨r₁, t₁, hr₁, hv⟩, -, q, q', s, t', a, hqy, hq, hat, hq', hqv⟩
    obtain ⟨hs, hb⟩ := (mem_type_iff hy hq).mp hqy
    obtain ⟨a₀, ha₀, hb₀⟩ := bis_pred hb hat
    have h1 : Bis s a r₁ t₁ := ((mem_type_iff hv hq').mp hqv).2
    exact ⟨a₀, ha₀, isType_of_bis hv (bis_trans (bis_symm h1) hb₀)⟩
  · rintro ⟨a, hat, hv⟩
    obtain ⟨q, hq⟩ := exists_pg r t
    obtain ⟨q', hq'⟩ := exists_pg r a
    exact ⟨⟨r, a, hr, hv⟩, ⟨r, t, hr, hy⟩, q, q', r, t, a,
      (mem_type_iff hy hq).mpr ⟨hr, bis_refl r t⟩, hq, hat, hq',
      (mem_type_iff hv hq').mpr ⟨hr, bis_refl r a⟩⟩

/-- **Extensionality for types.** -/
theorem ee_ext {x y : V} (hx : InZ x) (hy : InZ y) (h : ∀ v, EE v x ↔ EE v y) : x = y := by
  obtain ⟨r, t, hr, hx⟩ := hx
  obtain ⟨s, u, hs, hy⟩ := hy
  obtain ⟨B, hB⟩ := exists_rel 0 (((bisD.comp (τ' := ![0, 0, 3, 3, 0, 0]) ![2, 0, 3, 1] 0).or
    ((SDef.eq 0 4).and (SDef.eq 1 5)))) ![r, s, t, u]
  have hB' : ∀ a a', Rl B a a' ↔ Bis r a s a' ∨ (a = t ∧ a' = u) := hB
  have key : Bis r t s u := by
    refine ⟨B, fun a a' h1 => ?_, (hB' t u).mpr (Or.inr ⟨rfl, rfl⟩)⟩
    rcases (hB' a a').mp h1 with h2 | ⟨rfl, rfl⟩
    · exact ⟨fun b hb => let ⟨b', hb', h3⟩ := bis_pred h2 hb; ⟨b', hb', (hB' b b').mpr (Or.inl h3)⟩,
        fun b' hb' => let ⟨b, hb, h3⟩ := bis_pred (bis_symm h2) hb';
          ⟨b, hb, (hB' b b').mpr (Or.inl (bis_symm h3))⟩⟩
    · constructor
      · intro b hb
        obtain ⟨v, hv⟩ := exists_type r b
        obtain ⟨b', hb', hv'⟩ := (ee_iff hs hy).mp ((h v).mp ((ee_iff hr hx).mpr ⟨b, hb, hv⟩))
        exact ⟨b', hb', (hB' b b').mpr (Or.inl (bis_of_type hr hv hv'))⟩
      · intro b' hb'
        obtain ⟨v, hv⟩ := exists_type s b'
        obtain ⟨b, hb, hv'⟩ := (ee_iff hr hx).mp ((h v).mpr ((ee_iff hs hy).mpr ⟨b', hb', hv⟩))
        exact ⟨b, hb, (hB' b b').mpr (Or.inl (bis_of_type hr hv' hv))⟩
  exact type_unique (isType_of_bis hx key) hy

/-- **Foundation for types.** A set that contains a type has a type with no member in it. -/
theorem ee_wf (S : V) (h : ∃ x, x ∈ S ∧ InZ x) :
    ∃ x, x ∈ S ∧ InZ x ∧ ∀ y, y ∈ S → ¬ EE y x := by
  obtain ⟨x₀, hx₀, r, t, hr, hx⟩ := h
  obtain ⟨A, hA⟩ := (SDef.ex (τ := ![0, 7, 3]) 6
    ((SDef.mem 0 2).and (isTypeD.comp ![0, 3, 1] 0))).comprehension ![S, r]
  have hA' : ∀ a, a ∈ A ↔ ∃ v, v ∈ S ∧ IsType v r a := hA
  obtain ⟨a, ha, hmin⟩ := hr A ⟨t, (hA' t).mpr ⟨x₀, hx₀, hx⟩⟩
  obtain ⟨v, hvS, hv⟩ := (hA' a).mp ha
  refine ⟨v, hvS, ⟨r, a, hr, hv⟩, fun y hyS hyv => ?_⟩
  obtain ⟨b, hb, hy⟩ := (ee_iff hr hv).mp hyv
  exact hmin b ((hA' b).mpr ⟨y, hyS, hy⟩) hb

end model

end Hin

end FFL.FirstOrder.SetTheory
