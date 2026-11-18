import NFRel
import NFInterpretations

set_option autoImplicit false

/-!
# The types of well-founded pointed graphs in a model of `𝗡𝗙`, continued

`g` is the graph of the membership relation `EE` on types (`IsEg g`), and `θ x` is the type of
`g` pointed at `x`; `IsType y g x` says `y = θ x`. The map `θ` raises types, so it is not a set.

* `theta_mem`: the members of `θ x` are the `θ u` for the members `u` of `x`.
  `theta_inj`: `θ` is one-to-one on types.
* `theta_sup`: for every set `S` of types there is a type whose members are the `θ s`, `s ∈ S`.
  `full`: every set of types of the form `θ x` is the extension of a type.
* A set `X` of types is *stable* if `θ` maps it onto itself (`Stable g X`). Every subset of a
  stable set is the extension of a type (`stable_full`), and the set of the types all of whose
  members are in `X` is stable again (`pow_stable`).
* `InOm`: the finite ordinals among the types; they form a stable transitive set
  (`om_stable`). This uses that the universe is not finite, to find a new node.
* `Dom x`: `x` belongs to a stable transitive set. This is the domain of the interpretation.
-/

namespace FFL.FirstOrder.SetTheory

namespace Hin

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `θ` maps `X`, a set of types, onto itself. -/
def Stable (g X : V) : Prop :=
  (∀ x, x ∈ X → InZ x) ∧ (∀ x, x ∈ X → ∀ y, IsType y g x → y ∈ X) ∧
    ∀ y, y ∈ X → ∃ x, x ∈ X ∧ IsType y g x

/-- The members of the members of `X` are members of `X`. -/
def Trans (X : V) : Prop := ∀ x, x ∈ X → ∀ v, EE v x → v ∈ X

/-- **The domain of the interpretation**: the types that belong to a stable transitive set. -/
def Dom (x : V) : Prop := ∃ g X : V, IsEg g ∧ Stable g X ∧ Trans X ∧ x ∈ X

/-- A type without members. -/
def IsZero (z : V) : Prop := InZ z ∧ ∀ v, ¬ EE v z

/-- The members of `w` are `y` and the members of `y`. -/
def Succ (y w : V) : Prop := InZ y ∧ InZ w ∧ ∀ u, EE u w ↔ (EE u y ∨ u = y)

/-- `X` contains the types without members and is closed under successor. -/
def Ind (X : V) : Prop := (∀ z, IsZero z → z ∈ X) ∧ ∀ y, y ∈ X → ∀ w, Succ y w → w ∈ X

/-- `x` is a finite ordinal among the types. -/
def InOm (x : V) : Prop := ∀ X : V, Ind X → x ∈ X

/-- `N` is finite: it belongs to every family that contains the empty sets and is closed under
adjoining one element. -/
def FinS (N : V) : Prop := ∀ F : V, (∀ e : V, (∀ z : V, z ∉ e) → e ∈ F) →
  (∀ s : V, s ∈ F → ∀ b s' : V, (∀ z : V, z ∈ s' ↔ z ∈ s ∨ z = b) → s' ∈ F) → N ∈ F

/-- `x` is the type of a well-founded pointed graph whose nodes lie in a finite set. -/
def HasFin (x : V) : Prop := ∃ r t N : V, WF r ∧ IsType x r t ∧ FinS N ∧ t ∈ N ∧
  ∀ a b, Rl r a b → a ∈ N ∧ b ∈ N

end defs

section sdefs

def isZeroD : SDef ![6] (fun _ _ v ↦ IsZero (v 0)) :=
  ((inZD.comp ![0] 0).and (SDef.all 6 (eeD.comp ![0, 1] 0).not)).congr fun _ _ _ => Iff.rfl

def succD : SDef ![6, 6] (fun _ _ v ↦ Succ (v 0) (v 1)) :=
  ((inZD.comp ![0] 0).and ((inZD.comp ![1] 0).and (SDef.all 6
    ((eeD.comp ![0, 2] 0).iff ((eeD.comp ![0, 1] 0).or (SDef.eq 0 1)))))).congr
    fun _ _ _ => Iff.rfl

def indD : SDef ![7] (fun _ _ v ↦ Ind (v 0)) :=
  ((SDef.all 6 ((isZeroD.comp ![0] 0).imp (SDef.mem 0 1))).and
    (SDef.all 6 ((SDef.mem 0 1).imp (SDef.all 6 ((succD.comp ![1, 0] 0).imp
      (SDef.mem 0 2)))))).congr fun _ _ _ => Iff.rfl

def inOmD : SDef ![6] (fun _ _ v ↦ InOm (v 0)) :=
  (SDef.all 7 ((indD.comp ![0] 0).imp (SDef.mem 1 0))).congr fun _ _ _ => Iff.rfl

def finSD : SDef ![1] (fun _ _ v ↦ FinS (v 0)) :=
  (SDef.all 2 ((SDef.all 1 ((SDef.all 0 (SDef.mem 0 1).not).imp (SDef.mem 0 1))).imp
    ((SDef.all 1 ((SDef.mem 0 1).imp (SDef.all 0 (SDef.all 1
      ((SDef.all 0 ((SDef.mem 0 1).iff ((SDef.mem 0 3).or (SDef.eq 0 2)))).imp
        (SDef.mem 0 3)))))).imp (SDef.mem 1 0)))).congr fun _ _ _ => Iff.rfl

def hasFinD : SDef ![6] (fun _ _ v ↦ HasFin (v 0)) :=
  (SDef.ex 3 (SDef.ex 0 (SDef.ex 1 ((wfD.comp ![2] 0).and ((isTypeD.comp ![3, 2, 1] 0).and
    ((finSD.comp ![0] 0).and ((SDef.mem 1 0).and (SDef.all 0 (SDef.all 0
      ((rlD.comp ![4, 1, 0] 0).imp ((SDef.mem 1 2).and (SDef.mem 0 2)))))))))))).congr
    fun _ _ _ => Iff.rfl

end sdefs

/-! ### The graph of membership and the map `θ` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

theorem exists_empty : ∃ e : V, ∀ z, z ∉ e := by
  obtain ⟨e, he⟩ := ((SDef.eq (τ := ![0]) 0 0).not).comprehension (![] : Fin 0 → V)
  exact ⟨e, fun z hz => (he z).mp hz rfl⟩

theorem exists_eg : ∃ g : V, IsEg g :=
  (SDef.ex (τ := ![8]) 6 (SDef.ex 6
    ((isOpD.comp ![2, 1, 0] 6).and (eeD.comp ![1, 0] 0)))).comprehension (![] : Fin 0 → V)

theorem rl_eg {g : V} (hg : IsEg g) (u v : V) : Rl g u v ↔ EE u v := rl_of_spec hg u v

theorem eg_unique {g g' : V} (hg : IsEg g) (hg' : IsEg g') : g = g' :=
  nf_ext fun p => (hg p).trans (hg' p).symm

theorem wf_eg {g : V} (hg : IsEg g) : WF g := by
  rintro X ⟨c₀, hc₀⟩
  by_cases h : ∃ c, c ∈ X ∧ ¬ InZ c
  · obtain ⟨c, hc, hcz⟩ := h
    exact ⟨c, hc, fun b _ hb => hcz ((rl_eg hg b c).mp hb).2.1⟩
  · have h' : ∀ c, c ∈ X → InZ c := fun c hc => by
      by_contra hn; exact h ⟨c, hc, hn⟩
    obtain ⟨x, hx, -, hmin⟩ := ee_wf X ⟨c₀, hc₀, h' c₀ hc₀⟩
    exact ⟨x, hx, fun b hb hbx => hmin b hb ((rl_eg hg b x).mp hbx)⟩

/-- **The members of `θ x`** are the `θ u` for the members `u` of `x`. -/
theorem theta_mem {g y x v : V} (hg : IsEg g) (hy : IsType y g x) :
    EE v y ↔ ∃ u, EE u x ∧ IsType v g u :=
  (ee_iff (wf_eg hg) hy).trans
    (exists_congr fun u => and_congr (rl_eg hg u x) Iff.rfl)

theorem theta_inZ {g y x : V} (hg : IsEg g) (hy : IsType y g x) : InZ y :=
  ⟨g, x, wf_eg hg, hy⟩

/-- **`θ` is one-to-one on types.** -/
theorem theta_inj {g y x x' : V} (hg : IsEg g) (hy : IsType y g x) (hy' : IsType y g x')
    (hx : InZ x) (hx' : InZ x') : x = x' := by
  obtain ⟨B, hB, hxx⟩ := bis_of_type (wf_eg hg) hy hy'
  by_contra hne
  obtain ⟨C, hC⟩ := ((inZD.comp (τ' := ![6, 9]) ![0] 0).and (SDef.ex 6
    ((inZD.comp ![0] 0).and ((rlD.comp ![2, 1, 0] 6).and (SDef.eq 1 0).not)))).comprehension ![B]
  have hC' : ∀ u, u ∈ C ↔ InZ u ∧ ∃ v, InZ v ∧ Rl B u v ∧ ¬ u = v := hC
  obtain ⟨u, huC, huZ, hmin⟩ := ee_wf C ⟨x, (hC' x).mpr ⟨hx, x', hx', hxx, hne⟩, hx⟩
  obtain ⟨-, v, hvZ, huv, hne'⟩ := (hC' u).mp huC
  refine hne' (ee_ext huZ hvZ fun w => ⟨fun hw => ?_, fun hw => ?_⟩)
  · obtain ⟨w', hw', hww⟩ := (hB u v huv).1 w ((rl_eg hg w u).mpr hw)
    have hw'E : EE w' v := (rl_eg hg w' v).mp hw'
    have : w = w' := by
      by_contra hn
      exact hmin w ((hC' w).mpr ⟨hw.1, w', hw'E.1, hww, hn⟩) hw
    rw [this]; exact hw'E
  · obtain ⟨w₀, hw₀, hww⟩ := (hB u v huv).2 w ((rl_eg hg w v).mpr hw)
    have hw₀E : EE w₀ u := (rl_eg hg w₀ u).mp hw₀
    have : w₀ = w := by
      by_contra hn
      exact hmin w₀ ((hC' w₀).mpr ⟨hw₀E.1, w, hw.1, hww, hn⟩) hw₀E
    rw [← this]; exact hw₀E

/-- **For every set `S` of types there is a type whose members are the `θ s` for `s ∈ S`.** The
graph is that of membership with one more node, the empty set, above the members of `S`. -/
theorem theta_sup {g : V} (hg : IsEg g) (S : V) (hS : ∀ s, s ∈ S → InZ s) :
    ∃ w, InZ w ∧ ∀ v, EE v w ↔ ∃ s, s ∈ S ∧ IsType v g s := by
  obtain ⟨e, he⟩ := exists_empty (V := V)
  have heZ : ¬ InZ e := fun h => let ⟨q, hq⟩ := inZ_nonempty h; he q hq
  obtain ⟨ρ, hρ⟩ := exists_rel 6 ((eeD.comp (τ' := ![6, 6, 7, 6]) ![0, 1] 0).or
    ((SDef.mem 0 2).and (SDef.eq 1 3))) ![S, e]
  have hρ' : ∀ a b, Rl ρ a b ↔ EE a b ∨ (a ∈ S ∧ b = e) := hρ
  have hwf : WF ρ := by
    rintro X ⟨c₀, hc₀⟩
    by_cases h : ∃ c, c ∈ X ∧ ¬ c = e
    · obtain ⟨c₁, hc₁, hne⟩ := h
      obtain ⟨X', hX⟩ := ((SDef.mem (τ := ![6, 7, 6]) 0 1).and
        (SDef.eq 0 2).not).comprehension ![X, e]
      have hX' : ∀ c, c ∈ X' ↔ c ∈ X ∧ ¬ c = e := hX
      obtain ⟨c, hc, hmin⟩ := wf_eg hg X' ⟨c₁, (hX' c₁).mpr ⟨hc₁, hne⟩⟩
      obtain ⟨hcX, hce⟩ := (hX' c).mp hc
      refine ⟨c, hcX, fun b hb hbc => ?_⟩
      rcases (hρ' b c).mp hbc with h1 | ⟨-, h2⟩
      · have hbe : ¬ b = e := fun hb' => heZ (hb' ▸ h1.1)
        exact hmin b ((hX' b).mpr ⟨hb, hbe⟩) ((rl_eg hg b c).mpr h1)
      · exact hce h2
    · have h' : ∀ c, c ∈ X → c = e := fun c hc => by
        by_contra hn; exact h ⟨c, hc, hn⟩
      refine ⟨c₀, hc₀, fun b hb hbc => ?_⟩
      rw [h' b hb, h' c₀ hc₀] at hbc
      rcases (hρ' e e).mp hbc with h1 | ⟨h1, -⟩
      · exact heZ h1.1
      · exact heZ (hS e h1)
  obtain ⟨w, hw⟩ := exists_type ρ e
  obtain ⟨B, hB⟩ := exists_rel 6 ((SDef.eq (τ := ![6, 6]) 0 1).and (inZD.comp ![0] 0))
    (![] : Fin 0 → V)
  have hB' : ∀ a b, Rl B a b ↔ a = b ∧ InZ a := hB
  have hbis : ∀ a, InZ a → Bis ρ a g a := by
    intro a ha
    refine ⟨B, fun a₁ a₂ h12 => ?_, (hB' a a).mpr ⟨rfl, ha⟩⟩
    obtain ⟨rfl, ha₁⟩ := (hB' a₁ a₂).mp h12
    constructor
    · intro b hb
      rcases (hρ' b a₁).mp hb with h1 | ⟨-, h2⟩
      · exact ⟨b, (rl_eg hg b a₁).mpr h1, (hB' b b).mpr ⟨rfl, h1.1⟩⟩
      · exact absurd (h2 ▸ ha₁) heZ
    · intro b hb
      have h1 := (rl_eg hg b a₁).mp hb
      exact ⟨b, (hρ' b a₁).mpr (Or.inl h1), (hB' b b).mpr ⟨rfl, h1.1⟩⟩
  refine ⟨w, ⟨ρ, e, hwf, hw⟩, fun v => (ee_iff hwf hw).trans ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, hv⟩
    rcases (hρ' a e).mp ha with h1 | ⟨h1, -⟩
    · exact absurd h1.2.1 heZ
    · exact ⟨a, h1, isType_of_bis hv (hbis a (hS a h1))⟩
  · rintro ⟨s, hs, hv⟩
    exact ⟨s, (hρ' s e).mpr (Or.inr ⟨hs, rfl⟩), isType_of_bis hv (bis_symm (hbis s (hS s hs)))⟩

/-- **Every set of types of the form `θ x` is the extension of a type.** -/
theorem full {g : V} (hg : IsEg g) (S : V) (hS : ∀ s, s ∈ S → ∃ x, InZ x ∧ IsType s g x) :
    ∃ w, InZ w ∧ ∀ v, EE v w ↔ v ∈ S := by
  obtain ⟨S', hS'⟩ := ((inZD.comp (τ' := ![6, 13, 9]) ![0] 0).and (SDef.ex 12
    ((SDef.mem 0 2).and (isTypeD.comp ![0, 3, 1] 6)))).comprehension ![S, g]
  have hS'' : ∀ x, x ∈ S' ↔ InZ x ∧ ∃ s, s ∈ S ∧ IsType s g x := hS'
  obtain ⟨w, hwZ, hw⟩ := theta_sup hg S' fun s hs => ((hS'' s).mp hs).1
  refine ⟨w, hwZ, fun v => (hw v).trans ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, hv⟩
    obtain ⟨-, s, hs, hsx⟩ := (hS'' x).mp hx
    rw [type_unique hv hsx]; exact hs
  · intro hv
    obtain ⟨x, hxZ, hvx⟩ := hS v hv
    exact ⟨x, (hS'' x).mpr ⟨hxZ, v, hv, hvx⟩, hvx⟩

/-! ### Stable sets -/

/-- Every subset of a stable set is the extension of a type. -/
theorem stable_full {g X : V} (hg : IsEg g) (hX : Stable g X) (S : V)
    (hSX : ∀ s, s ∈ S → s ∈ X) : ∃ w, InZ w ∧ ∀ v, EE v w ↔ v ∈ S :=
  full hg S fun s hs => let ⟨x, hx, h⟩ := hX.2.2 s (hSX s hs); ⟨x, hX.1 x hx, h⟩

theorem exists_pow (X : V) : ∃ P : V, ∀ y, y ∈ P ↔ InZ y ∧ ∀ u, EE u y → u ∈ X :=
  ((inZD.comp (τ' := ![6, 7]) ![0] 0).and
    (SDef.all 6 ((eeD.comp ![0, 1] 0).imp (SDef.mem 0 2)))).comprehension ![X]

/-- **The types all of whose members are in a stable set form a stable set.** -/
theorem pow_stable {g X P : V} (hg : IsEg g) (hX : Stable g X)
    (hP : ∀ y, y ∈ P ↔ InZ y ∧ ∀ u, EE u y → u ∈ X) : Stable g P := by
  refine ⟨fun y hy => ((hP y).mp hy).1, fun y hy y' hy' => ?_, fun y hy => ?_⟩
  · obtain ⟨-, hyX⟩ := (hP y).mp hy
    refine (hP y').mpr ⟨theta_inZ hg hy', fun u hu => ?_⟩
    obtain ⟨u₀, hu₀, huu⟩ := (theta_mem hg hy').mp hu
    exact hX.2.1 u₀ (hyX u₀ hu₀) u huu
  · obtain ⟨hyZ, hyX⟩ := (hP y).mp hy
    obtain ⟨S', hS'⟩ := ((SDef.mem (τ := ![6, 7, 12, 9]) 0 1).and (SDef.ex 12
      ((eeD.comp ![0, 3] 6).and (isTypeD.comp ![0, 4, 1] 6)))).comprehension ![X, y, g]
    have hS'' : ∀ u, u ∈ S' ↔ u ∈ X ∧ ∃ v, EE v y ∧ IsType v g u := hS'
    obtain ⟨w, hwZ, hw⟩ := stable_full hg hX S' fun s hs => ((hS'' s).mp hs).1
    have hwP : w ∈ P := (hP w).mpr ⟨hwZ, fun u hu => ((hS'' u).mp ((hw u).mp hu)).1⟩
    obtain ⟨y', hy'⟩ := exists_type g w
    have e : y' = y := ee_ext (theta_inZ hg hy') hyZ fun v => (theta_mem hg hy').trans ⟨?_, ?_⟩
    · exact ⟨w, hwP, e ▸ hy'⟩
    · rintro ⟨u, hu, hvu⟩
      obtain ⟨-, v₀, hv₀, hv₀u⟩ := (hS'' u).mp ((hw u).mp hu)
      rw [type_unique hvu hv₀u]; exact hv₀
    · intro hv
      obtain ⟨u, huX, hvu⟩ := hX.2.2 v (hyX v hv)
      exact ⟨u, (hw u).mpr ((hS'' u).mpr ⟨huX, v, hv, hvu⟩), hvu⟩

omit [Nonempty V] hT in
theorem pow_trans {g X P : V} (hX : Stable g X) (hXt : Trans X)
    (hP : ∀ y, y ∈ P ↔ InZ y ∧ ∀ u, EE u y → u ∈ X) :
    (∀ x, x ∈ X → x ∈ P) ∧ Trans P := by
  have h1 : ∀ x, x ∈ X → x ∈ P := fun x hx => (hP x).mpr ⟨hX.1 x hx, fun u hu => hXt x hx u hu⟩
  exact ⟨h1, fun y hy v hv => h1 v (((hP y).mp hy).2 v hv)⟩

theorem exists_union (X Y : V) : ∃ U : V, ∀ x, x ∈ U ↔ x ∈ X ∨ x ∈ Y :=
  ((SDef.mem (τ := ![6, 7, 7]) 0 1).or (SDef.mem 0 2)).comprehension ![X, Y]

omit [Nonempty V] hT in
theorem union_stable {g X Y U : V} (hX : Stable g X) (hY : Stable g Y)
    (hU : ∀ x, x ∈ U ↔ x ∈ X ∨ x ∈ Y) : Stable g U := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun y hy => ?_⟩
  · rcases (hU x).mp hx with h | h
    · exact hX.1 x h
    · exact hY.1 x h
  · rcases (hU x).mp hx with h | h
    · exact (hU y).mpr (Or.inl (hX.2.1 x h y hy))
    · exact (hU y).mpr (Or.inr (hY.2.1 x h y hy))
  · rcases (hU y).mp hy with h | h
    · obtain ⟨x, hx, hxy⟩ := hX.2.2 y h
      exact ⟨x, (hU x).mpr (Or.inl hx), hxy⟩
    · obtain ⟨x, hx, hxy⟩ := hY.2.2 y h
      exact ⟨x, (hU x).mpr (Or.inr hx), hxy⟩

omit [Nonempty V] hT in
theorem union_trans {X Y U : V} (hX : Trans X) (hY : Trans Y)
    (hU : ∀ x, x ∈ U ↔ x ∈ X ∨ x ∈ Y) : Trans U := by
  intro x hx v hv
  rcases (hU x).mp hx with h | h
  · exact (hU v).mpr (Or.inl (hX x h v hv))
  · exact (hU v).mpr (Or.inr (hY x h v hv))

/-! ### Finite sets and a new node -/

omit [Nonempty V] hT in
theorem fin_empty {e : V} (he : ∀ z, z ∉ e) : FinS e := fun _ h0 _ => h0 e he

omit [Nonempty V] hT in
theorem fin_adj {s s' b : V} (hs : FinS s) (h : ∀ z, z ∈ s' ↔ z ∈ s ∨ z = b) : FinS s' :=
  fun F h0 h1 => h1 s (hs F h0 h1) b s' h

/-- **A finite set is not the universe**: this is where `𝗡𝗙 ⊢ Axiom.universeInfinite`, that is,
Specker's theorem, is used. -/
theorem exists_fresh {N : V} (hN : FinS N) : ∃ c, c ∉ N := by
  have h0 : V↓[ℒₛₑₜ] ⊧ Axiom.universeInfinite := models_of_provable hT nf_provable_universeInfinite
  have key : ∃ F : V, (∀ e : V, (∀ z, z ∉ e) → e ∈ F) ∧
      (∀ s ∈ F, ∀ b s' : V, (∀ z, z ∈ s' ↔ z ∈ s ∨ z = b) → s' ∈ F) ∧
      ∀ u : V, (∀ z, z ∈ u) → u ∉ F := by
    simpa [models_iff, Axiom.universeInfinite] using h0
  obtain ⟨F, h1, h2, h3⟩ := key
  by_contra hn
  exact h3 N (fun z => by by_contra hz; exact hn ⟨z, hz⟩) (hN F h1 h2)

/-! ### Zero and successor -/

theorem exists_zero : ∃ z : V, IsZero z := by
  obtain ⟨e, he⟩ := exists_empty (V := V)
  have hwf : WF e := fun X ⟨c, hc⟩ => ⟨c, hc, fun b _ ⟨p, hp, _⟩ => he p hp⟩
  obtain ⟨z, hz⟩ := exists_type e e
  exact ⟨z, ⟨e, e, hwf, hz⟩, fun v hv =>
    let ⟨a, ⟨p, hp, _⟩, _⟩ := (ee_iff hwf hz).mp hv; he p hp⟩

theorem zero_unique {z z' : V} (h : IsZero z) (h' : IsZero z') : z = z' :=
  ee_ext h.1 h'.1 fun v => ⟨fun hv => absurd hv (h.2 v), fun hv => absurd hv (h'.2 v)⟩

theorem succ_unique {y w w' : V} (h : Succ y w) (h' : Succ y w') : w = w' :=
  ee_ext h.2.1 h'.2.1 fun v => (h.2.2 v).trans (h'.2.2 v).symm

/-- A type with finitely many nodes has a successor with finitely many nodes: add a new node
above the top and its predecessors. -/
theorem succ_of_hasFin {y : V} (hy : HasFin y) : ∃ w, Succ y w ∧ HasFin w := by
  obtain ⟨r, t, N, hr, hyt, hN, htN, hNr⟩ := hy
  obtain ⟨c, hc⟩ := exists_fresh hN
  obtain ⟨r', hr'⟩ := exists_rel 0 ((rlD.comp (τ' := ![0, 0, 3, 0, 0]) ![2, 0, 1] 0).or
    ((SDef.eq 1 4).and ((rlD.comp ![2, 0, 3] 0).or (SDef.eq 0 3)))) ![r, t, c]
  have hr'' : ∀ a b, Rl r' a b ↔ Rl r a b ∨ (b = c ∧ (Rl r a t ∨ a = t)) := hr'
  obtain ⟨N', hN'⟩ := ((SDef.mem (τ := ![0, 1, 0]) 0 1).or (SDef.eq 0 2)).comprehension ![N, c]
  have hN'' : ∀ z, z ∈ N' ↔ z ∈ N ∨ z = c := hN'
  have hwf : WF r' := by
    rintro X ⟨c₀, hc₀⟩
    by_cases h : ∃ d, d ∈ X ∧ ¬ d = c
    · obtain ⟨d₁, hd₁, hne⟩ := h
      obtain ⟨X', hX⟩ := ((SDef.mem (τ := ![0, 1, 0]) 0 1).and
        (SDef.eq 0 2).not).comprehension ![X, c]
      have hX' : ∀ d, d ∈ X' ↔ d ∈ X ∧ ¬ d = c := hX
      obtain ⟨d, hd, hmin⟩ := hr X' ⟨d₁, (hX' d₁).mpr ⟨hd₁, hne⟩⟩
      obtain ⟨hdX, hdc⟩ := (hX' d).mp hd
      refine ⟨d, hdX, fun b hb hbd => ?_⟩
      rcases (hr'' b d).mp hbd with h1 | ⟨h1, -⟩
      · have hbc : ¬ b = c := fun e => hc (e ▸ (hNr b d h1).1)
        exact hmin b ((hX' b).mpr ⟨hb, hbc⟩) h1
      · exact hdc h1
    · have h' : ∀ d, d ∈ X → d = c := fun d hd => by
        by_contra hn; exact h ⟨d, hd, hn⟩
      refine ⟨c₀, hc₀, fun b hb hbc => ?_⟩
      rw [h' b hb, h' c₀ hc₀] at hbc
      rcases (hr'' c c).mp hbc with h1 | ⟨-, h1 | h1⟩
      · exact hc (hNr c c h1).1
      · exact hc (hNr c t h1).1
      · exact hc (h1 ▸ htN)
  obtain ⟨B, hB⟩ := exists_rel 0 ((SDef.eq (τ := ![0, 0, 1]) 0 1).and (SDef.mem 0 2)) ![N]
  have hB' : ∀ a b, Rl B a b ↔ a = b ∧ a ∈ N := hB
  have hbis : ∀ a, a ∈ N → Bis r a r' a := by
    intro a ha
    refine ⟨B, fun a₁ a₂ h12 => ?_, (hB' a a).mpr ⟨rfl, ha⟩⟩
    obtain ⟨rfl, ha₁⟩ := (hB' a₁ a₂).mp h12
    constructor
    · intro b hb
      exact ⟨b, (hr'' b a₁).mpr (Or.inl hb), (hB' b b).mpr ⟨rfl, (hNr b a₁ hb).1⟩⟩
    · intro b hb
      rcases (hr'' b a₁).mp hb with h1 | ⟨h1, -⟩
      · exact ⟨b, h1, (hB' b b).mpr ⟨rfl, (hNr b a₁ h1).1⟩⟩
      · exact absurd (h1 ▸ ha₁) hc
  obtain ⟨w, hw⟩ := exists_type r' c
  refine ⟨w, ⟨⟨r, t, hr, hyt⟩, ⟨r', c, hwf, hw⟩, fun u => (ee_iff hwf hw).trans ⟨?_, ?_⟩⟩,
    r', c, N', hwf, hw, fin_adj hN hN'', (hN'' c).mpr (Or.inr rfl), fun a b hab => ?_⟩
  · rintro ⟨a, ha, hu⟩
    rcases (hr'' a c).mp ha with h1 | ⟨-, h1 | h1⟩
    · exact absurd (hNr a c h1).2 hc
    · exact Or.inl ((ee_iff hr hyt).mpr
        ⟨a, h1, isType_of_bis hu (bis_symm (hbis a (hNr a t h1).1))⟩)
    · subst h1
      exact Or.inr (type_unique (isType_of_bis hu (bis_symm (hbis a htN))) hyt)
  · rintro (hu | rfl)
    · obtain ⟨a, ha, hua⟩ := (ee_iff hr hyt).mp hu
      exact ⟨a, (hr'' a c).mpr (Or.inr ⟨rfl, Or.inl ha⟩),
        isType_of_bis hua (hbis a (hNr a t ha).1)⟩
    · exact ⟨t, (hr'' t c).mpr (Or.inr ⟨rfl, Or.inr rfl⟩), isType_of_bis hyt (hbis t htN)⟩
  · rcases (hr'' a b).mp hab with h1 | ⟨h1, h2 | h2⟩
    · exact ⟨(hN'' a).mpr (Or.inl (hNr a b h1).1), (hN'' b).mpr (Or.inl (hNr a b h1).2)⟩
    · exact ⟨(hN'' a).mpr (Or.inl (hNr a t h2).1), (hN'' b).mpr (Or.inr h1)⟩
    · exact ⟨(hN'' a).mpr (Or.inl (h2 ▸ htN)), (hN'' b).mpr (Or.inr h1)⟩

theorem zero_hasFin {z : V} (hz : IsZero z) : HasFin z := by
  obtain ⟨e, he⟩ := exists_empty (V := V)
  have hwf : WF e := fun X ⟨c, hc⟩ => ⟨c, hc, fun b _ ⟨p, hp, _⟩ => he p hp⟩
  obtain ⟨z', hz'⟩ := exists_type e e
  have h0 : IsZero z' := ⟨⟨e, e, hwf, hz'⟩, fun v hv =>
    let ⟨a, ⟨p, hp, _⟩, _⟩ := (ee_iff hwf hz').mp hv; he p hp⟩
  obtain rfl := zero_unique hz h0
  obtain ⟨N, hN⟩ := exists_sing e
  exact ⟨e, e, N, hwf, hz', fin_adj (fin_empty he) (b := e)
    (fun z => (hN z).trans ⟨Or.inr, fun h => h.resolve_left (he z)⟩), mem_sing hN,
    fun a b ⟨p, hp, _⟩ => absurd hp (he p)⟩

/-! ### The finite ordinals -/

omit [Nonempty V] hT in
theorem om_zero {z : V} (hz : IsZero z) : InOm z := fun _ hX => hX.1 z hz

omit [Nonempty V] hT in
theorem om_succ {y w : V} (hy : InOm y) (h : Succ y w) : InOm w :=
  fun X hX => hX.2 y (hy X hX) w h

/-- Induction over the finite ordinals, for a condition with a stratified definition. -/
theorem om_ind (c : ℕ) {k : ℕ} {τ : Fin k → ℕ} {R : URel (k + 1)} (d : SDef ((6 + c) :> τ) R)
    (p : Fin k → V)
    (h0 : ∀ z, IsZero z → R V (z :> p))
    (h1 : ∀ y, InOm y → R V (y :> p) → ∀ w, Succ y w → R V (w :> p)) :
    ∀ x, InOm x → R V (x :> p) := by
  have hf : ∀ i, ((6 + c) :> τ) (![0] i) = ![6] i + c := by intro i; fin_cases i; rfl
  obtain ⟨Y, hY⟩ := ((inOmD.comp (τ' := (6 + c) :> τ) ![0] c hf).and d).comprehension p
  have hY' : ∀ x, x ∈ Y ↔ InOm x ∧ R V (x :> p) := hY
  have hInd : Ind Y := ⟨fun z hz => (hY' z).mpr ⟨om_zero hz, h0 z hz⟩, fun y hy w hw =>
    (hY' w).mpr ⟨om_succ ((hY' y).mp hy).1 hw, h1 y ((hY' y).mp hy).1 ((hY' y).mp hy).2 w hw⟩⟩
  exact fun x hx => ((hY' x).mp (hx Y hInd)).2

theorem om_inZ {x : V} (hx : InOm x) : InZ x :=
  om_ind 0 (inZD) (![] : Fin 0 → V) (fun _ hz => hz.1) (fun _ _ _ _ hw => hw.2.1) x hx

theorem om_trans {x u : V} (hx : InOm x) (hu : EE u x) : InOm u := by
  have := om_ind 0 (SDef.all (τ := ![6]) 6 ((eeD.comp ![0, 1] 0).imp (inOmD.comp ![0] 0)))
    (![] : Fin 0 → V) (fun z hz u hu => absurd hu (hz.2 u))
    (fun y hy ih w hw u hu => by
      rcases (hw.2.2 u).mp hu with h | rfl
      · exact ih u h
      · exact hy) x hx
  exact this u hu

theorem om_hasFin {x : V} (hx : InOm x) : HasFin x :=
  om_ind 0 hasFinD (![] : Fin 0 → V) (fun _ hz => zero_hasFin hz)
    (fun _ _ ih w hw => by
      obtain ⟨w', hw', hfin⟩ := succ_of_hasFin ih
      rw [succ_unique hw hw']; exact hfin) x hx

theorem om_succ_exists {y : V} (hy : InOm y) : ∃ w, Succ y w ∧ InOm w :=
  let ⟨w, hw, _⟩ := succ_of_hasFin (om_hasFin hy); ⟨w, hw, om_succ hy hw⟩

/-- `θ` commutes with successor. -/
theorem succ_theta {g x w y y' : V} (hg : IsEg g) (hy : IsType y g x) (hy' : IsType y' g w)
    (h : Succ x w) : Succ y y' := by
  refine ⟨theta_inZ hg hy, theta_inZ hg hy', fun v => (theta_mem hg hy').trans ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu, hvu⟩
    rcases (h.2.2 u).mp hu with h1 | rfl
    · exact Or.inl ((theta_mem hg hy).mpr ⟨u, h1, hvu⟩)
    · exact Or.inr (type_unique hvu hy)
  · rintro (hv | rfl)
    · obtain ⟨u, hu, hvu⟩ := (theta_mem hg hy).mp hv
      exact ⟨u, (h.2.2 u).mpr (Or.inl hu), hvu⟩
    · exact ⟨x, (h.2.2 x).mpr (Or.inr rfl), hy⟩

theorem zero_theta {g z y : V} (hg : IsEg g) (hz : IsZero z) (hy : IsType y g z) : IsZero y :=
  ⟨theta_inZ hg hy, fun v hv => let ⟨u, hu, _⟩ := (theta_mem hg hy).mp hv; hz.2 u hu⟩

/-- **The finite ordinals form a stable transitive set.** -/
theorem om_stable {g : V} (hg : IsEg g) :
    ∃ Ω : V, (∀ x, x ∈ Ω ↔ InOm x) ∧ Stable g Ω ∧ Trans Ω := by
  obtain ⟨Ω, hΩ⟩ := inOmD.comprehension (![] : Fin 0 → V)
  have hΩ' : ∀ x, x ∈ Ω ↔ InOm x := hΩ
  refine ⟨Ω, hΩ', ⟨fun x hx => om_inZ ((hΩ' x).mp hx), fun x hx y hy => ?_, fun y hy => ?_⟩,
    fun x hx v hv => (hΩ' v).mpr (om_trans ((hΩ' x).mp hx) hv)⟩
  · have := om_ind 0 (SDef.all (τ := ![6, 9]) 12
      ((isTypeD.comp ![0, 2, 1] 6).imp (inOmD.comp ![0] 6))) ![g]
      (fun z hz y hy => om_zero (zero_theta hg hz hy))
      (fun x₁ _ ih w hw y' hy' => by
        obtain ⟨y₁, hy₁⟩ := exists_type g x₁
        exact om_succ (ih y₁ hy₁) (succ_theta hg hy₁ hy' hw)) x ((hΩ' x).mp hx)
    exact (hΩ' y).mpr (this y hy)
  · have := om_ind 6 (SDef.ex (τ := ![12, 9]) 6
      ((inOmD.comp ![0] 0).and (isTypeD.comp ![1, 2, 0] 6))) ![g]
      (fun z hz => by
        obtain ⟨y₀, hy₀⟩ := exists_type g z
        have e : y₀ = z := zero_unique (zero_theta hg hz hy₀) hz
        exact ⟨z, om_zero hz, e ▸ hy₀⟩)
      (fun y₁ _ ih w hw => by
        obtain ⟨x₁, hx₁, hyx⟩ := ih
        obtain ⟨x₂, hx₂, hx₂om⟩ := om_succ_exists hx₁
        obtain ⟨y₂, hy₂⟩ := exists_type g x₂
        have e : y₂ = w := succ_unique (succ_theta hg hyx hy₂ hx₂) hw
        exact ⟨x₂, hx₂om, e ▸ hy₂⟩) y ((hΩ' y).mp hy)
    obtain ⟨x, hx, hyx⟩ := this
    exact ⟨x, (hΩ' x).mpr hx, hyx⟩

end model

end Hin

end FFL.FirstOrder.SetTheory
