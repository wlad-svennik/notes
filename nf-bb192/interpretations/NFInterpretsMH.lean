import NFInterpretsMac
import MHTheory

set_option autoImplicit false

/-!
# NF interprets Mac Lane set theory with the collapse axiom

The model of `𝗠` inside a model of `𝗡𝗙` (`NFInterpretsMac.lean`) consists of the types of
well-founded pointed graphs that belong to a stable transitive set. It satisfies the collapse
axiom of `MHTheory.lean`.

Let `u` be a set of the model and `X` a stable transitive set that contains it. The members of
`u` are types; `θ` maps `X` onto itself, so there is a set `U⁻` of the `x ∈ X` with `θ x` a
member of `u`. The bound for `u` is the set `T` of the types of all well-founded pointed graphs
on `U⁻`. Given a well-founded relation `r` on `u` in the sense of the model, pull it back along
`θ` to a graph `ρ` on `U⁻`; the collapse sends the member `θ x` of `u` to the type of `(ρ, x)`.
It is a set of the model because `θ x` and the type of a graph pointed at `x` have the same
type in the sense of stratification.

* `typeOn_stable`: the types of the well-founded pointed graphs on a stable set form a stable
  transitive set.
* `hc_of_embed`: the collapse axiom holds in the model.
* `nfInterpretsMH : 𝗡𝗙 ⊳ 𝗠𝗛`.
-/

namespace FFL.FirstOrder.SetTheory

namespace Hin

/-! ### Pairs in the sense of the membership relation on types -/

section defs

variable {V : Type} [SetStructure V]

/-- The only member of `s` is `a`. -/
def SingE (s a : V) : Prop := EE a s ∧ ∀ c, EE c s → c = a

/-- The members of `d` are `a` and `b`. -/
def UpE (d a b : V) : Prop := EE a d ∧ EE b d ∧ ∀ c, EE c d → c = a ∨ c = b

/-- `p` is the pair of `a` and `b`. -/
def OpE (p a b : V) : Prop :=
  (∃ s, EE s p ∧ SingE s a) ∧ (∃ d, EE d p ∧ UpE d a b) ∧ ∀ z, EE z p → SingE z a ∨ UpE z a b

/-- The pair of `a` and `b` is a member of `r`. -/
def PrE (r a b : V) : Prop := ∃ p, EE p r ∧ OpE p a b

/-- `t` is the type of a well-founded pointed graph on `A`. -/
def TypeOn (A t : V) : Prop :=
  ∃ ρ x, WF ρ ∧ (∀ a b, Rl ρ a b → a ∈ A ∧ b ∈ A) ∧ x ∈ A ∧ IsType t ρ x

end defs

def singED : SDef ![6, 6] (fun _ _ v ↦ SingE (v 0) (v 1)) :=
  ((eeD.comp (τ' := ![6, 6]) ![1, 0] 0).and
    (SDef.all 6 ((eeD.comp ![0, 1] 0).imp (SDef.eq 0 2)))).congr fun _ _ _ => Iff.rfl

def upED : SDef ![6, 6, 6] (fun _ _ v ↦ UpE (v 0) (v 1) (v 2)) :=
  ((eeD.comp (τ' := ![6, 6, 6]) ![1, 0] 0).and ((eeD.comp ![2, 0] 0).and
    (SDef.all 6 ((eeD.comp ![0, 1] 0).imp ((SDef.eq 0 2).or (SDef.eq 0 3)))))).congr
    fun _ _ _ => Iff.rfl

def opED : SDef ![6, 6, 6] (fun _ _ v ↦ OpE (v 0) (v 1) (v 2)) :=
  ((SDef.ex (τ := ![6, 6, 6]) 6 ((eeD.comp ![0, 1] 0).and (singED.comp ![0, 2] 0))).and
    ((SDef.ex 6 ((eeD.comp ![0, 1] 0).and (upED.comp ![0, 2, 3] 0))).and
      (SDef.all 6 ((eeD.comp ![0, 1] 0).imp
        ((singED.comp ![0, 2] 0).or (upED.comp ![0, 2, 3] 0)))))).congr fun _ _ _ => Iff.rfl

def prED : SDef ![6, 6, 6] (fun _ _ v ↦ PrE (v 0) (v 1) (v 2)) :=
  (SDef.ex (τ := ![6, 6, 6]) 6 ((eeD.comp ![0, 1] 0).and (opED.comp ![0, 2, 3] 0))).congr
    fun _ _ _ => Iff.rfl

def typeOnD : SDef ![1, 6] (fun _ _ v ↦ TypeOn (v 0) (v 1)) :=
  (SDef.ex (τ := ![1, 6]) 3 (SDef.ex 0 ((wfD.comp ![1] 0).and
    ((SDef.all 0 (SDef.all 0 ((rlD.comp ![3, 1, 0] 0).imp
      ((SDef.mem 1 4).and (SDef.mem 0 4))))).and
      ((SDef.mem 0 2).and (isTypeD.comp ![3, 1, 0] 0)))))).congr fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- The type of a pointed graph depends only on the edges of the graph. -/
theorem isType_congr {y r r' t : V} (h : ∀ a b, Rl r a b ↔ Rl r' a b) (hy : IsType y r t) :
    IsType y r' t := by
  obtain ⟨B, hB⟩ := exists_rel (k := 0) (τ := ![]) 0 (SDef.eq 0 1) (![] : Fin 0 → V)
  have hB' : ∀ a b, Rl B a b ↔ a = b := hB
  refine isType_of_bis hy ⟨B, fun a a' haa => ?_, (hB' t t).mpr rfl⟩
  have e : a = a' := (hB' a a').mp haa
  subst e
  exact ⟨fun b hb => ⟨b, (h b a).mp hb, (hB' b b).mpr rfl⟩,
    fun b hb => ⟨b, (h b a).mpr hb, (hB' b b).mpr rfl⟩⟩

/-- **`θ` of the type of a pointed graph on types** is the type of the image of the graph
under `θ`, pointed at the image of the point. -/
theorem theta_type {g ρ ρ' x x' t y : V} (hg : IsEg g) (hρ : WF ρ)
    (hZ : ∀ a b, Rl ρ a b → InZ a ∧ InZ b) (hxZ : InZ x)
    (hρ' : ∀ a' b', Rl ρ' a' b' ↔ ∃ a b, Rl ρ a b ∧ IsType a' g a ∧ IsType b' g b)
    (hx' : IsType x' g x) (ht : IsType t ρ x) (hy : IsType y g t) :
    WF ρ' ∧ IsType y ρ' x' := by
  constructor
  · intro Y ⟨c₀, hc₀⟩
    obtain ⟨Y₀, hY₀⟩ := ((inZD.comp (τ' := ![6, 13, 9]) ![0] 0).and (SDef.ex 12
      ((SDef.mem 0 2).and (isTypeD.comp ![0, 3, 1] 6)))).comprehension ![Y, g]
    have hY₀' : ∀ a, a ∈ Y₀ ↔ InZ a ∧ ∃ c, c ∈ Y ∧ IsType c g a := hY₀
    by_cases hne : ∃ a, a ∈ Y₀
    · obtain ⟨a, ha, hmin⟩ := hρ Y₀ hne
      obtain ⟨haZ, c, hc, hca⟩ := (hY₀' a).mp ha
      refine ⟨c, hc, fun b hb hbc => ?_⟩
      obtain ⟨b₁, a₁, hba, hb1, hc1⟩ := (hρ' b c).mp hbc
      have e : a₁ = a := theta_inj hg hc1 hca (hZ _ _ hba).2 haZ
      subst e
      exact hmin b₁ ((hY₀' b₁).mpr ⟨(hZ _ _ hba).1, b, hb, hb1⟩) hba
    · refine ⟨c₀, hc₀, fun b hb hbc => hne ?_⟩
      obtain ⟨b₁, a₁, hba, hb1, hc1⟩ := (hρ' b c₀).mp hbc
      exact ⟨a₁, (hY₀' a₁).mpr ⟨(hZ _ _ hba).2, c₀, hc₀, hc1⟩⟩
  · obtain ⟨B, hB⟩ := exists_rel (τ := ![9, 9]) 12 (SDef.ex 6 ((inZD.comp ![0] 0).and
      ((isTypeD.comp ![1, 3, 0] 6).and (isTypeD.comp ![2, 4, 0] 6)))) ![ρ, g]
    have hB' : ∀ s a', Rl B s a' ↔ ∃ a, InZ a ∧ IsType s ρ a ∧ IsType a' g a := hB
    refine isType_of_bis hy ⟨B, fun s a' hsa => ?_, (hB' t x').mpr ⟨x, hxZ, ht, hx'⟩⟩
    obtain ⟨a, haZ, hs, ha'⟩ := (hB' s a').mp hsa
    constructor
    · intro u hu
      obtain ⟨b, hba, hub⟩ := (ee_iff hρ hs).mp ((rl_eg hg u s).mp hu)
      obtain ⟨b', hb'⟩ := exists_type g b
      exact ⟨b', (hρ' b' a').mpr ⟨b, a, hba, hb', ha'⟩, (hB' u b').mpr ⟨b, (hZ _ _ hba).1, hub, hb'⟩⟩
    · intro b' hb'
      obtain ⟨b₁, a₁, hba, hb1, ha1⟩ := (hρ' b' a').mp hb'
      have e : a₁ = a := theta_inj hg ha1 ha' (hZ _ _ hba).2 haZ
      subst e
      obtain ⟨u, hu⟩ := exists_type ρ b₁
      exact ⟨u, (rl_eg hg u s).mpr ((ee_iff hρ hs).mpr ⟨b₁, hba, hu⟩),
        (hB' u b').mpr ⟨b₁, (hZ _ _ hba).1, hu, hb1⟩⟩

/-- **The types of the well-founded pointed graphs on a stable set form a stable transitive
set.** -/
theorem typeOn_stable {g X ZX : V} (hg : IsEg g) (hX : Stable g X)
    (hZX : ∀ t, t ∈ ZX ↔ TypeOn X t) : Stable g ZX ∧ Trans ZX := by
  refine ⟨⟨fun t ht => ?_, fun t ht y hy => ?_, fun t ht => ?_⟩, fun t ht v hv => ?_⟩
  · obtain ⟨ρ, x, hρ, -, -, htx⟩ := (hZX t).mp ht
    exact ⟨ρ, x, hρ, htx⟩
  · obtain ⟨ρ, x, hρ, hed, hx, htx⟩ := (hZX t).mp ht
    obtain ⟨ρ', hρ'⟩ := exists_rel (τ := ![3, 3]) 6 (SDef.ex 0 (SDef.ex 0
      ((rlD.comp ![4, 1, 0] 0).and ((isTypeD.comp ![2, 5, 1] 0).and
        (isTypeD.comp ![3, 5, 0] 0))))) ![ρ, g]
    have hρ'' : ∀ a' b', Rl ρ' a' b' ↔ ∃ a b, Rl ρ a b ∧ IsType a' g a ∧ IsType b' g b :=
      fun a' b' => (hρ' a' b').trans ⟨fun ⟨a, b, h1, h2, h3⟩ => ⟨a, b, h1, h2, h3⟩,
        fun ⟨a, b, h1, h2, h3⟩ => ⟨a, b, h1, h2, h3⟩⟩
    obtain ⟨x', hx'⟩ := exists_type g x
    obtain ⟨hwf, hyt⟩ := theta_type hg hρ
      (fun a b h => ⟨hX.1 a (hed a b h).1, hX.1 b (hed a b h).2⟩) (hX.1 x hx) hρ'' hx' htx hy
    refine (hZX y).mpr ⟨ρ', x', hwf, fun a' b' h => ?_, hX.2.1 x hx x' hx', hyt⟩
    obtain ⟨a, b, hab, ha, hb⟩ := (hρ'' a' b').mp h
    exact ⟨hX.2.1 a (hed a b hab).1 a' ha, hX.2.1 b (hed a b hab).2 b' hb⟩
  · obtain ⟨ρ, x, hρ, hed, hx, htx⟩ := (hZX t).mp ht
    obtain ⟨ρ₀, hρ₀⟩ := exists_rel (τ := ![7, 9, 15]) 6 ((SDef.mem 0 2).and ((SDef.mem 1 2).and
      (SDef.ex 12 (SDef.ex 12 ((isTypeD.comp ![1, 5, 2] 6).and ((isTypeD.comp ![0, 5, 3] 6).and
        (rlD.comp ![6, 1, 0] 12))))))) ![X, g, ρ]
    have hρ₀' : ∀ a₀ b₀, Rl ρ₀ a₀ b₀ ↔ a₀ ∈ X ∧ b₀ ∈ X ∧
        ∃ a b, IsType a g a₀ ∧ IsType b g b₀ ∧ Rl ρ a b :=
      fun a₀ b₀ => (hρ₀ a₀ b₀).trans ⟨fun ⟨h1, h2, a, b, h3, h4, h5⟩ => ⟨h1, h2, a, b, h3, h4, h5⟩,
        fun ⟨h1, h2, a, b, h3, h4, h5⟩ => ⟨h1, h2, a, b, h3, h4, h5⟩⟩
    obtain ⟨x₀, hx₀, hxx₀⟩ := hX.2.2 x hx
    have hwf₀ : WF ρ₀ := by
      intro Y ⟨c₀, hc₀⟩
      obtain ⟨Y', hY'⟩ := (SDef.ex (τ := ![12, 7, 7, 9]) 6 ((SDef.mem 0 2).and
        ((SDef.mem 0 3).and (isTypeD.comp ![1, 4, 0] 6)))).comprehension ![Y, X, g]
      have hY'' : ∀ a, a ∈ Y' ↔ ∃ a₀, a₀ ∈ Y ∧ a₀ ∈ X ∧ IsType a g a₀ := hY'
      by_cases hne : ∃ a, a ∈ Y'
      · obtain ⟨a, ha, hmin⟩ := hρ Y' hne
        obtain ⟨a₀, ha₀Y, ha₀X, haa₀⟩ := (hY'' a).mp ha
        refine ⟨a₀, ha₀Y, fun b₀ hb₀ hba => ?_⟩
        obtain ⟨hb₀X, -, p, q, hp, hq, hpq⟩ := (hρ₀' b₀ a₀).mp hba
        have e : q = a := type_unique hq haa₀
        subst e
        exact hmin p ((hY'' p).mpr ⟨b₀, hb₀, hb₀X, hp⟩) hpq
      · refine ⟨c₀, hc₀, fun b₀ hb₀ hbc => hne ?_⟩
        obtain ⟨-, hc₀X, p, q, hp, hq, hpq⟩ := (hρ₀' b₀ c₀).mp hbc
        exact ⟨q, (hY'' q).mpr ⟨c₀, hc₀, hc₀X, hq⟩⟩
    obtain ⟨t₀, ht₀⟩ := exists_type ρ₀ x₀
    have ht₀Z : t₀ ∈ ZX := (hZX t₀).mpr ⟨ρ₀, x₀, hwf₀,
      fun a b h => ⟨((hρ₀' a b).mp h).1, ((hρ₀' a b).mp h).2.1⟩, hx₀, ht₀⟩
    refine ⟨t₀, ht₀Z, ?_⟩
    obtain ⟨ρ', hρ'⟩ := exists_rel (τ := ![3, 3]) 6 (SDef.ex 0 (SDef.ex 0
      ((rlD.comp ![4, 1, 0] 0).and ((isTypeD.comp ![2, 5, 1] 0).and
        (isTypeD.comp ![3, 5, 0] 0))))) ![ρ₀, g]
    have hρ'' : ∀ a' b', Rl ρ' a' b' ↔ ∃ a b, Rl ρ₀ a b ∧ IsType a' g a ∧ IsType b' g b :=
      fun a' b' => (hρ' a' b').trans ⟨fun ⟨a, b, h1, h2, h3⟩ => ⟨a, b, h1, h2, h3⟩,
        fun ⟨a, b, h1, h2, h3⟩ => ⟨a, b, h1, h2, h3⟩⟩
    obtain ⟨y₀, hy₀⟩ := exists_type g t₀
    obtain ⟨-, hy₀t⟩ := theta_type hg hwf₀
      (fun a b h => ⟨hX.1 a ((hρ₀' a b).mp h).1, hX.1 b ((hρ₀' a b).mp h).2.1⟩) (hX.1 x₀ hx₀)
      hρ'' hxx₀ ht₀ hy₀
    have hsame : ∀ a b, Rl ρ' a b ↔ Rl ρ a b := by
      intro a b
      constructor
      · intro h
        obtain ⟨a₀, b₀, h0, ha, hb⟩ := (hρ'' a b).mp h
        obtain ⟨-, -, p, q, hp, hq, hpq⟩ := (hρ₀' a₀ b₀).mp h0
        rw [type_unique ha hp, type_unique hb hq]
        exact hpq
      · intro h
        obtain ⟨a₀, ha₀, haa₀⟩ := hX.2.2 a (hed a b h).1
        obtain ⟨b₀, hb₀, hbb₀⟩ := hX.2.2 b (hed a b h).2
        exact (hρ'' a b).mpr ⟨a₀, b₀, (hρ₀' a₀ b₀).mpr ⟨ha₀, hb₀, a, b, haa₀, hbb₀, h⟩, haa₀, hbb₀⟩
    have e : y₀ = t := type_unique (isType_congr hsame hy₀t) htx
    rw [← e]
    exact hy₀
  · obtain ⟨ρ, x, hρ, hed, hx, htx⟩ := (hZX t).mp ht
    obtain ⟨a, hax, hva⟩ := (ee_iff hρ htx).mp hv
    exact (hZX v).mpr ⟨ρ, a, hρ, hed, (hed a x hax).1, hva⟩

end model

/-! ### The collapse axiom in the model -/

section base

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- **The collapse axiom holds for the types in `Dom`**, with membership `EE`. -/
theorem hc_of_embed {W : Type} [SetStructure W] (i : W → M) (hi : Function.Injective i)
    (hdom : ∀ x : M, Dom x ↔ ∃ w, i w = x) (hmem : ∀ a b : W, a ∈ b ↔ EE (i a) (i b)) :
    MH.HC W := by
  have hbase : IsMacBase W := isMacBase_of_embed i hi hdom hmem
  obtain ⟨g, hg⟩ := exists_eg (V := M)
  have dom_iff : ∀ x : M, Dom x ↔ ∃ X, Stable g X ∧ Trans X ∧ x ∈ X := fun x =>
    ⟨fun ⟨g', X, hg', h⟩ => ⟨X, by rw [eg_unique hg hg']; exact h⟩, fun ⟨X, h⟩ => ⟨g, X, hg, h⟩⟩
  have hdomi : ∀ w, Dom (i w) := fun w => (hdom _).mpr ⟨w, rfl⟩
  have hdown : ∀ w v, EE v (i w) → ∃ w', i w' = v := fun w v hv => by
    obtain ⟨X, hX, hXt, hx⟩ := (dom_iff _).mp (hdomi w)
    exact (hdom v).mp ((dom_iff v).mpr ⟨X, hX, hXt, hXt _ hx v hv⟩)
  have key : ∀ X S : M, Stable g X → Trans X → (∀ s, s ∈ S → s ∈ X) →
      ∃ w : W, ∀ v, EE v (i w) ↔ v ∈ S := by
    intro X S hX hXt hS
    obtain ⟨y, hyZ, hy⟩ := stable_full hg hX S hS
    obtain ⟨P, hP⟩ := exists_pow X
    have hyP : y ∈ P := (hP y).mpr ⟨hyZ, fun u hu => hS u ((hy u).mp hu)⟩
    obtain ⟨w, rfl⟩ := (hdom y).mp
      ((dom_iff y).mpr ⟨P, pow_stable hg hX hP, (pow_trans hX hXt hP).2, hyP⟩)
    exact ⟨w, hy⟩
  -- pairs in `W` and in the model
  have hS : ∀ s a : W, MH.IsSing s a ↔ SingE (i s) (i a) := fun s a =>
    ⟨fun ⟨h1, h2⟩ => ⟨(hmem a s).mp h1, fun c hc => by
      obtain ⟨c', rfl⟩ := hdown s c hc
      rw [h2 c' ((hmem c' s).mpr hc)]⟩,
    fun ⟨h1, h2⟩ => ⟨(hmem a s).mpr h1, fun c hc => hi (h2 _ ((hmem c s).mp hc))⟩⟩
  have hU : ∀ d a b : W, MH.IsUp d a b ↔ UpE (i d) (i a) (i b) := fun d a b =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨(hmem a d).mp h1, (hmem b d).mp h2, fun c hc => by
      obtain ⟨c', rfl⟩ := hdown d c hc
      rcases h3 c' ((hmem c' d).mpr hc) with e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (by rw [e])⟩,
    fun ⟨h1, h2, h3⟩ => ⟨(hmem a d).mpr h1, (hmem b d).mpr h2, fun c hc =>
      (h3 _ ((hmem c d).mp hc)).imp (fun e => hi e) (fun e => hi e)⟩⟩
  have hO : ∀ p a b : W, MH.IsOp p a b ↔ OpE (i p) (i a) (i b) := fun p a b =>
    ⟨fun ⟨⟨s, hs, hsa⟩, ⟨d, hd, hdab⟩, h3⟩ =>
      ⟨⟨i s, (hmem s p).mp hs, (hS s a).mp hsa⟩, ⟨i d, (hmem d p).mp hd, (hU d a b).mp hdab⟩,
        fun z hz => by
          obtain ⟨z', rfl⟩ := hdown p z hz
          exact (h3 z' ((hmem z' p).mpr hz)).imp (hS z' a).mp (hU z' a b).mp⟩,
    fun ⟨⟨s, hs, hsa⟩, ⟨d, hd, hdab⟩, h3⟩ => by
      obtain ⟨s', rfl⟩ := hdown p s hs
      obtain ⟨d', rfl⟩ := hdown p d hd
      exact ⟨⟨s', (hmem s' p).mpr hs, (hS s' a).mpr hsa⟩,
        ⟨d', (hmem d' p).mpr hd, (hU d' a b).mpr hdab⟩,
        fun z hz => (h3 _ ((hmem z p).mp hz)).imp (hS z a).mpr (hU z a b).mpr⟩⟩
  have hP : ∀ r a b : W, MH.Pr r a b ↔ PrE (i r) (i a) (i b) := fun r a b =>
    ⟨fun ⟨p, hp, hop⟩ => ⟨i p, (hmem p r).mp hp, (hO p a b).mp hop⟩,
    fun ⟨p, hp, hop⟩ => by
      obtain ⟨p', rfl⟩ := hdown r p hp
      exact ⟨p', (hmem p' r).mpr hp, (hO p' a b).mpr hop⟩⟩
  have hpairW : ∀ a b : W, ∃ p : W, MH.IsOp p a b := by
    intro a b
    obtain ⟨s, hs⟩ := hbase.pairing a a
    obtain ⟨d, hd⟩ := hbase.pairing a b
    obtain ⟨p, hp⟩ := hbase.pairing s d
    have hsa : MH.IsSing s a := ⟨(hs a).mpr (Or.inl rfl), fun c hc => ((hs c).mp hc).elim id id⟩
    have hdab : MH.IsUp d a b :=
      ⟨(hd a).mpr (Or.inl rfl), (hd b).mpr (Or.inr rfl), fun c hc => (hd c).mp hc⟩
    exact ⟨p, ⟨s, (hp s).mpr (Or.inl rfl), hsa⟩, ⟨d, (hp d).mpr (Or.inr rfl), hdab⟩,
      fun z hz => by
        rcases (hp z).mp hz with rfl | rfl
        · exact Or.inl hsa
        · exact Or.inr hdab⟩
  intro u
  obtain ⟨X, hX, hXt, hu⟩ := (dom_iff _).mp (hdomi u)
  have huX : ∀ a, EE a (i u) → a ∈ X := fun a ha => hXt _ hu a ha
  obtain ⟨ZX, hZX⟩ := (typeOnD.comp (τ' := ![6, 1]) ![1, 0] 0).comprehension ![X]
  have hZX' : ∀ t, t ∈ ZX ↔ TypeOn X t := hZX
  obtain ⟨hZXs, hZXt⟩ := typeOn_stable hg hX hZX'
  obtain ⟨Um, hUm⟩ := ((SDef.mem (τ := ![6, 7, 12, 9]) 0 1).and (SDef.ex 12
    ((eeD.comp ![0, 3] 6).and (isTypeD.comp ![0, 4, 1] 6)))).comprehension ![X, i u, g]
  have hUm' : ∀ x, x ∈ Um ↔ x ∈ X ∧ ∃ a, EE a (i u) ∧ IsType a g x := hUm
  obtain ⟨Zs, hZs⟩ := (typeOnD.comp (τ' := ![6, 1]) ![1, 0] 0).comprehension ![Um]
  have hZs' : ∀ t, t ∈ Zs ↔ TypeOn Um t := hZs
  have hZsZX : ∀ t, t ∈ Zs → t ∈ ZX := fun t ht => by
    obtain ⟨ρ, x, hρ, hed, hx, htx⟩ := (hZs' t).mp ht
    exact (hZX' t).mpr ⟨ρ, x, hρ, fun a b h => ⟨((hUm' a).mp (hed a b h).1).1,
      ((hUm' b).mp (hed a b h).2).1⟩, ((hUm' x).mp hx).1, htx⟩
  have hZXdom : ∀ t, t ∈ ZX → ∃ w, i w = t := fun t ht =>
    (hdom t).mp ((dom_iff t).mpr ⟨ZX, hZXs, hZXt, ht⟩)
  obtain ⟨T, hT'⟩ := key ZX Zs hZXs hZXt hZsZX
  refine ⟨T, fun y hy z hz => ?_, fun r hr => ?_⟩
  · -- `T` is transitive
    obtain ⟨ρ, x, hρ, hed, hx, hyx⟩ := (hZs' _).mp ((hT' _).mp ((hmem y T).mp hy))
    obtain ⟨a, hax, hza⟩ := (ee_iff hρ hyx).mp ((hmem z y).mp hz)
    exact (hmem z T).mpr ((hT' _).mpr ((hZs' _).mpr ⟨ρ, a, hρ, hed, (hed a x hax).1, hza⟩))
  · -- the graph on `Um`
    obtain ⟨ρ, hρ⟩ := exists_rel (τ := ![1, 3, 6]) 0 ((SDef.mem 0 2).and ((SDef.mem 1 2).and
      (SDef.ex 6 (SDef.ex 6 ((isTypeD.comp ![1, 5, 2] 0).and ((isTypeD.comp ![0, 5, 3] 0).and
        (prED.comp ![6, 1, 0] 0))))))) ![Um, g, i r]
    have hρ' : ∀ x y, Rl ρ x y ↔ x ∈ Um ∧ y ∈ Um ∧
        ∃ a b, IsType a g x ∧ IsType b g y ∧ PrE (i r) a b :=
      fun x y => (hρ x y).trans ⟨fun ⟨h1, h2, a, b, h3, h4, h5⟩ => ⟨h1, h2, a, b, h3, h4, h5⟩,
        fun ⟨h1, h2, a, b, h3, h4, h5⟩ => ⟨h1, h2, a, b, h3, h4, h5⟩⟩
    have hρwf : WF ρ := by
      intro Y ⟨c₀, hc₀⟩
      by_cases hsub : ∀ c, c ∈ Y → c ∈ Um
      · obtain ⟨S, hS0⟩ := ((eeD.comp (τ' := ![6, 6, 1, 3]) ![0, 1] 0).and (SDef.ex 0
          ((SDef.mem 0 3).and (isTypeD.comp ![1, 4, 0] 0)))).comprehension ![i u, Y, g]
        have hS' : ∀ a, a ∈ S ↔ EE a (i u) ∧ ∃ x, x ∈ Y ∧ IsType a g x := hS0
        obtain ⟨wS, hwS⟩ := key X S hX hXt fun s hs => huX s ((hS' s).mp hs).1
        obtain ⟨a₀, ha₀u, ha₀⟩ := ((hUm' c₀).mp (hsub c₀ hc₀)).2
        obtain ⟨w₀, rfl⟩ := hdown u a₀ ha₀u
        obtain ⟨c, hc, hmin⟩ := hr wS
          ⟨w₀, (hmem w₀ wS).mpr ((hwS _).mpr ((hS' _).mpr ⟨ha₀u, c₀, hc₀, ha₀⟩)), id⟩
          (fun c hc => (hmem c u).mpr ((hS' _).mp ((hwS _).mp ((hmem c wS).mp hc))).1)
        obtain ⟨-, x, hxY, hcx⟩ := (hS' _).mp ((hwS _).mp ((hmem c wS).mp hc))
        refine ⟨x, hxY, fun b₀ hb₀ hb₀x => ?_⟩
        obtain ⟨hb₀U, -, a, b, ha, hb, hab⟩ := (hρ' b₀ x).mp hb₀x
        have e : b = i c := type_unique hb hcx
        subst e
        obtain ⟨-, a', ha'u, ha'⟩ := (hUm' b₀).mp hb₀U
        have e : a = a' := type_unique ha ha'
        subst e
        obtain ⟨wa, rfl⟩ := hdown u a ha'u
        exact hmin wa ((hmem wa wS).mpr ((hwS _).mpr ((hS' _).mpr ⟨ha'u, b₀, hb₀, ha⟩)))
          ((hP r wa c).mpr hab)
      · have hsub' : ∃ c, c ∈ Y ∧ c ∉ Um := by
          by_contra hcon
          exact hsub fun c hc => by
            by_contra hcU
            exact hcon ⟨c, hc, hcU⟩
        obtain ⟨c, hc, hcU⟩ := hsub'
        exact ⟨c, hc, fun b _ hbc => hcU ((hρ' b c).mp hbc).2.1⟩
    -- the collapse as a set of pairs
    obtain ⟨SF, hSF⟩ := (SDef.ex (τ := ![6, 6, 1, 3, 3]) 6 (SDef.ex 6 (SDef.ex 0
      ((eeD.comp ![2, 4] 0).and ((SDef.mem 0 5).and ((isTypeD.comp ![2, 6, 0] 0).and
        ((isTypeD.comp ![1, 7, 0] 0).and (opED.comp ![3, 2, 1] 0)))))))).comprehension
      ![i u, X, g, ρ]
    have hSF' : ∀ p, p ∈ SF ↔ ∃ b t x, EE b (i u) ∧ x ∈ X ∧ IsType b g x ∧ IsType t ρ x ∧
        OpE p b t := hSF
    obtain ⟨Y, hY⟩ := exists_union X ZX
    have hYs : Stable g Y := union_stable hX hZXs hY
    have hYt : Trans Y := union_trans hXt hZXt hY
    obtain ⟨P1, hP1⟩ := exists_pow Y
    have hP1s : Stable g P1 := pow_stable hg hYs hP1
    have hP1t : Trans P1 := (pow_trans hYs hYt hP1).2
    obtain ⟨P2, hP2⟩ := exists_pow P1
    have hP2s : Stable g P2 := pow_stable hg hP1s hP2
    have hP2t : Trans P2 := (pow_trans hP1s hP1t hP2).2
    have htype : ∀ x, x ∈ Um → ∀ t, IsType t ρ x → t ∈ Zs := fun x hx t ht =>
      (hZs' t).mpr ⟨ρ, x, hρwf, fun a b h => ⟨((hρ' a b).mp h).1, ((hρ' a b).mp h).2.1⟩, hx, ht⟩
    have hSFsub : ∀ p, p ∈ SF → p ∈ P2 := by
      intro p hp
      obtain ⟨b, t, x, hbu, hxX, hbx, htx, hop⟩ := (hSF' p).mp hp
      have hbY : b ∈ Y := (hY b).mpr (Or.inl (huX b hbu))
      have htY : t ∈ Y := (hY t).mpr (Or.inr (hZsZX t
        (htype x ((hUm' x).mpr ⟨hxX, b, hbu, hbx⟩) t htx)))
      obtain ⟨⟨s, hsp, -⟩, -, hall⟩ := hop
      refine (hP2 p).mpr ⟨hsp.2.1, fun z hz => (hP1 z).mpr ⟨hz.1, fun c hc => ?_⟩⟩
      rcases hall z hz with h | h
      · rw [h.2 c hc]; exact hbY
      · rcases h.2.2 c hc with e | e
        · rw [e]; exact hbY
        · rw [e]; exact htY
    obtain ⟨F, hF⟩ := key P2 SF hP2s hP2t hSFsub
    have hFiff : ∀ a y : W, MH.Pr F a y ↔
        a ∈ u ∧ ∃ x, x ∈ X ∧ IsType (i a) g x ∧ IsType (i y) ρ x := by
      intro a y
      constructor
      · rintro ⟨p, hp, hop⟩
        obtain ⟨b, t, x, hbu, hxX, hbx, htx, hop'⟩ := (hSF' _).mp ((hF _).mp ((hmem p F).mp hp))
        obtain ⟨b', rfl⟩ := hdown u b hbu
        obtain ⟨t', rfl⟩ := hZXdom t (hZsZX t (htype x ((hUm' x).mpr ⟨hxX, _, hbu, hbx⟩) t htx))
        obtain ⟨rfl, rfl⟩ := MH.op_inj hop ((hO p b' t').mpr hop')
        exact ⟨(hmem a u).mpr hbu, x, hxX, hbx, htx⟩
      · rintro ⟨hau, x, hxX, hax, hyx⟩
        obtain ⟨p, hp⟩ := hpairW a y
        exact ⟨p, (hmem p F).mpr ((hF _).mpr ((hSF' _).mpr
          ⟨i a, i y, x, (hmem a u).mp hau, hxX, hax, hyx, (hO p a y).mp hp⟩)), hp⟩
    refine ⟨F, fun b hb => ?_⟩
    have hbu : EE (i b) (i u) := (hmem b u).mp hb
    obtain ⟨xb, hxbX, hbxb⟩ := hX.2.2 (i b) (huX _ hbu)
    have hxbU : xb ∈ Um := (hUm' xb).mpr ⟨hxbX, i b, hbu, hbxb⟩
    obtain ⟨tb, htb⟩ := exists_type ρ xb
    obtain ⟨v, rfl⟩ := hZXdom tb (hZsZX tb (htype xb hxbU tb htb))
    refine ⟨v, (hmem v T).mpr ((hT' _).mpr (htype xb hxbU _ htb)),
      (hFiff b v).mpr ⟨hb, xb, hxbX, hbxb, htb⟩, fun v' hv' => ?_, fun y => ?_⟩
    · obtain ⟨-, x, hxX, hbx, hv'x⟩ := (hFiff b v').mp hv'
      have e : x = xb := theta_inj hg hbx hbxb (hX.1 x hxX) (hX.1 xb hxbX)
      subst e
      exact hi (type_unique hv'x htb)
    · rw [hmem y v, ee_iff hρwf htb]
      constructor
      · rintro ⟨x', hx'xb, hyx'⟩
        obtain ⟨hx'U, -, a', b', ha', hb', hab⟩ := (hρ' x' xb).mp hx'xb
        have e : b' = i b := type_unique hb' hbxb
        subst e
        obtain ⟨hx'X, a'', ha''u, ha''⟩ := (hUm' x').mp hx'U
        have e : a' = a'' := type_unique ha' ha''
        subst e
        obtain ⟨a, rfl⟩ := hdown u a' ha''u
        exact ⟨a, (hmem a u).mpr ha''u, (hP r a b).mpr hab,
          (hFiff a y).mpr ⟨(hmem a u).mpr ha''u, x', hx'X, ha', hyx'⟩⟩
      · rintro ⟨a, hau, hrab, hFay⟩
        obtain ⟨-, x, hxX, hax, hyx⟩ := (hFiff a y).mp hFay
        exact ⟨x, (hρ' x xb).mpr ⟨(hUm' x).mpr ⟨hxX, i a, (hmem a u).mp hau, hax⟩, hxbU,
          i a, i b, hax, hbxb, (hP r a b).mp hrab⟩, hyx⟩

end base

end Hin

/-! ### The interpretation -/

/-- A structure with the properties `IsMacBase` in which the collapse axiom holds is a model
of `𝗠𝗛`, when it is given with its relation symbols. -/
theorem MH.models' {W : Type} [SetStructure W] [Nonempty W] [s : Tarski.Structure ℒₛₑₜ W]
    [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W] (h : IsMacBase W)
    (hc : MH.HC W) : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := by
  rcases standardStructure_unique W s
  haveI : W↓[ℒₛₑₜ] ⊧* 𝗠 := h.models
  exact MH.models_of_hc hc

section

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- **In a model of `𝗡𝗙`, the interpreted structure is a model of `𝗠𝗛`.** -/
theorem macModel_models_mh : (macTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛 :=
  MH.models'
    (Hin.isMacBase_of_embed (fun a : macTranslation.Model M ↦ (a : M))
      (fun a b h => by cases a; cases b; cases h; rfl)
      (fun x => ⟨fun hx => ⟨⟨x, (macDomain_val_iff x).mpr hx⟩, rfl⟩,
        fun ⟨w, hw⟩ => hw ▸ (macDomain_val_iff _).mp w.dom⟩)
      macModel_mem_iff)
    (Hin.hc_of_embed (fun a : macTranslation.Model M ↦ (a : M))
      (fun a b h => by cases a; cases b; cases h; rfl)
      (fun x => ⟨fun hx => ⟨⟨x, (macDomain_val_iff x).mpr hx⟩, rfl⟩,
        fun ⟨w, hw⟩ => hw ▸ (macDomain_val_iff _).mp w.dom⟩)
      macModel_mem_iff)

end

/-- **`𝗡𝗙` interprets `𝗠𝗛`**: Mac Lane set theory with transitive containment and the collapse
axiom, without choice. The translation is that of `interpretsM`. -/
instance nfInterpretsMH : 𝗡𝗙 ⊳ 𝗠𝗛 where
  trln := macTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp macModel_models_mh φ hφ)

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.nfInterpretsMH
