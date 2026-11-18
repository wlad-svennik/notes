import MHExist

set_option autoImplicit false

/-!
# The order of the constructible sets

Inside a model `V` of `𝗠𝗛`.

* `RkL β x`: `x` appears first at stage `β`. `LtL x x'`: the order of the constructible sets:
  first by the stage at which they appear, then the level itself, then by least definitions.
* `lts_iff`: the order `LtS γ` of the level at `γ` is `LtL` on that level.
* `wo_lev`: `LtL` is total on every level, and every set of members of a level that has a
  member has a least member.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section defs

variable {V : Type} [SetStructure V]

/-- `lt` is total on `A`, and every subset of `A` in `P` with a member has a least member. -/
def WOr (A lt P : V) : Prop :=
  (∀ x, x ∈ A → ∀ y, y ∈ A → Pr lt x y ∨ (x = y ∨ Pr lt y x)) ∧
  (∀ Z, Z ∈ P → (∀ z, z ∈ Z → z ∈ A) → (∃ z, z ∈ Z ∧ ¬False) →
    ∃ m, m ∈ Z ∧ ∀ z, z ∈ Z → ¬Pr lt z m)

/-- The level of `f` at `β` is not well-ordered. -/
def NotWOAt (β f P : V) : Prop :=
  ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ d, d ∈ u ∧ ∃ w, w ∈ d ∧ ∃ A, A ∈ w ∧ ∃ w', w' ∈ d ∧
    ∃ lt, lt ∈ w' ∧ (IsOp q β d ∧ (IsOp d A lt ∧ ¬WOr A lt P))

end defs

def worB : BDef (k := 3) (fun V _ v ↦ WOr (v 0) (v 1) (v 2)) :=
  ((BDef.ball 0 (BDef.ball 1 ((prB.comp ![3, 1, 0]).or ((BDef.eq 1 0).or
    (prB.comp ![3, 0, 1]))))).and
  (BDef.ball 2 ((BDef.ball 0 (BDef.mem 0 2)).imp ((BDef.bex 0 BDef.fls.not).imp
    (BDef.bex 0 (BDef.ball 1 (prB.comp ![4, 0, 1]).not)))))).congr fun _ _ _ => Iff.rfl

def notWOAtB : BDef (k := 3) (fun V _ v ↦ NotWOAt (v 0) (v 1) (v 2)) :=
  (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0
    ((isOpB.comp ![6, 7, 4]).and ((isOpB.comp ![4, 2, 0]).and
      (worB.comp ![2, 0, 9]).not))))))))).congr fun _ _ _ => Iff.rfl

/-- The relation used to minimise over the least definitions of the members of a set. -/
def keyOfB : BDef (k := 7) (fun V _ v ↦ ∃ z, z ∈ v 6 ∧
    LeastD (v 4) (v 5) (v 0) (v 1) (v 2) (v 3) z) :=
  (BDef.bex 6 (leastDB.comp ![5, 6, 1, 2, 3, 4, 0])).congr fun _ _ _ => Iff.rfl

/-- The relation used to find the least definition of a set. -/
def defOfB : BDef (k := 7) (fun V _ v ↦ IsD (v 4) (v 5) (v 0) (v 1) (v 2) (v 3) (v 6)) :=
  (isDB.comp ![4, 5, 0, 1, 2, 3, 6]).congr fun _ _ _ => Iff.rfl

section lex

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- **The least four-tuple** with a property that has a bounded definition, in the
lexicographic order. -/
theorem lex4_min {Q : MRel 7} (d : BDef Q) {A lt : V} (p₀ p₁ p₂ : V)
    (hleast : ∀ Z : V, (∀ z, z ∈ Z → z ∈ A) → (∃ z, z ∈ Z) →
      ∃ m, m ∈ Z ∧ ∀ z, z ∈ Z → ¬Pr lt z m)
    (hex : ∃ a₀, a₀ ∈ A ∧ ∃ a₁, a₁ ∈ A ∧ ∃ a₂, a₂ ∈ A ∧ ∃ a₃, a₃ ∈ A ∧
      Q V ![a₀, a₁, a₂, a₃, p₀, p₁, p₂]) :
    ∃ a₀, a₀ ∈ A ∧ ∃ a₁, a₁ ∈ A ∧ ∃ a₂, a₂ ∈ A ∧ ∃ a₃, a₃ ∈ A ∧
      (Q V ![a₀, a₁, a₂, a₃, p₀, p₁, p₂] ∧ ∀ b₀, b₀ ∈ A → ∀ b₁, b₁ ∈ A → ∀ b₂, b₂ ∈ A →
        ∀ b₃, b₃ ∈ A → Q V ![b₀, b₁, b₂, b₃, p₀, p₁, p₂] → ¬Lex4 lt b₀ b₁ b₂ b₃ a₀ a₁ a₂ a₃) := by
  have e0 : ∀ a₀ a₁ a₂ a₃ : V, (fun i ↦ (a₃ :> a₂ :> a₁ :> a₀ :> ![A, p₀, p₁, p₂])
      (![3, 2, 1, 0, 5, 6, 7] i)) = ![a₀, a₁, a₂, a₃, p₀, p₁, p₂] := by
    intro a₀ a₁ a₂ a₃; funext i; fin_cases i <;> rfl
  have e1 : ∀ m₀ a₁ a₂ a₃ : V, (fun i ↦ (a₃ :> a₂ :> a₁ :> ![A, m₀, p₀, p₁, p₂])
      (![4, 2, 1, 0, 5, 6, 7] i)) = ![m₀, a₁, a₂, a₃, p₀, p₁, p₂] := by
    intro m₀ a₁ a₂ a₃; funext i; fin_cases i <;> rfl
  have e2 : ∀ m₀ m₁ a₂ a₃ : V, (fun i ↦ (a₃ :> a₂ :> ![A, m₀, m₁, p₀, p₁, p₂])
      (![3, 4, 1, 0, 5, 6, 7] i)) = ![m₀, m₁, a₂, a₃, p₀, p₁, p₂] := by
    intro m₀ m₁ a₂ a₃; funext i; fin_cases i <;> rfl
  have e3 : ∀ m₀ m₁ m₂ a₃ : V, (fun i ↦ (a₃ :> ![m₀, m₁, m₂, p₀, p₁, p₂])
      (![1, 2, 3, 0, 4, 5, 6] i)) = ![m₀, m₁, m₂, a₃, p₀, p₁, p₂] := by
    intro m₀ m₁ m₂ a₃; funext i; fin_cases i <;> rfl
  -- first coordinate
  let S₀ : V := sepB (k := 4) (BDef.bex 1 (BDef.bex 2 (BDef.bex 3
    (d.comp ![3, 2, 1, 0, 5, 6, 7])))) A ![A, p₀, p₁, p₂]
  have hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ A ∧ ∃ a₁, a₁ ∈ A ∧ ∃ a₂, a₂ ∈ A ∧ ∃ a₃, a₃ ∈ A ∧
      Q V ![a, a₁, a₂, a₃, p₀, p₁, p₂] := by
    intro a
    refine (mem_sepB _ _ _ a).trans (and_congr Iff.rfl (exists_congr fun a₁ => and_congr Iff.rfl
      (exists_congr fun a₂ => and_congr Iff.rfl (exists_congr fun a₃ => and_congr Iff.rfl ?_))))
    show Q V (fun i ↦ (a₃ :> a₂ :> a₁ :> a :> ![A, p₀, p₁, p₂]) (![3, 2, 1, 0, 5, 6, 7] i)) ↔ _
    rw [e0]
  obtain ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, hc⟩ := hex
  obtain ⟨m₀, hm₀, hmin₀⟩ := hleast S₀ (fun z hz => ((hS₀ z).mp hz).1)
    ⟨c₀, (hS₀ c₀).mpr ⟨hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, hc⟩⟩
  obtain ⟨hm₀A, d₁, hd₁, d₂, hd₂, d₃, hd₃, hdQ⟩ := (hS₀ m₀).mp hm₀
  -- second coordinate
  let S₁ : V := sepB (k := 5) (BDef.bex 1 (BDef.bex 2
    (d.comp ![4, 2, 1, 0, 5, 6, 7]))) A ![A, m₀, p₀, p₁, p₂]
  have hS₁ : ∀ a, a ∈ S₁ ↔ a ∈ A ∧ ∃ a₂, a₂ ∈ A ∧ ∃ a₃, a₃ ∈ A ∧
      Q V ![m₀, a, a₂, a₃, p₀, p₁, p₂] := by
    intro a
    refine (mem_sepB _ _ _ a).trans (and_congr Iff.rfl (exists_congr fun a₂ => and_congr Iff.rfl
      (exists_congr fun a₃ => and_congr Iff.rfl ?_)))
    show Q V (fun i ↦ (a₃ :> a₂ :> a :> ![A, m₀, p₀, p₁, p₂]) (![4, 2, 1, 0, 5, 6, 7] i)) ↔ _
    rw [e1]
  obtain ⟨m₁, hm₁, hmin₁⟩ := hleast S₁ (fun z hz => ((hS₁ z).mp hz).1)
    ⟨d₁, (hS₁ d₁).mpr ⟨hd₁, d₂, hd₂, d₃, hd₃, hdQ⟩⟩
  obtain ⟨hm₁A, f₂, hf₂, f₃, hf₃, hfQ⟩ := (hS₁ m₁).mp hm₁
  -- third coordinate
  let S₂ : V := sepB (k := 6) (BDef.bex 1
    (d.comp ![3, 4, 1, 0, 5, 6, 7])) A ![A, m₀, m₁, p₀, p₁, p₂]
  have hS₂ : ∀ a, a ∈ S₂ ↔ a ∈ A ∧ ∃ a₃, a₃ ∈ A ∧ Q V ![m₀, m₁, a, a₃, p₀, p₁, p₂] := by
    intro a
    refine (mem_sepB _ _ _ a).trans (and_congr Iff.rfl (exists_congr fun a₃ =>
      and_congr Iff.rfl ?_))
    show Q V (fun i ↦ (a₃ :> a :> ![A, m₀, m₁, p₀, p₁, p₂]) (![3, 4, 1, 0, 5, 6, 7] i)) ↔ _
    rw [e2]
  obtain ⟨m₂, hm₂, hmin₂⟩ := hleast S₂ (fun z hz => ((hS₂ z).mp hz).1)
    ⟨f₂, (hS₂ f₂).mpr ⟨hf₂, f₃, hf₃, hfQ⟩⟩
  obtain ⟨hm₂A, g₃, hg₃, hgQ⟩ := (hS₂ m₂).mp hm₂
  -- fourth coordinate
  let S₃ : V := sepB (k := 6) (d.comp ![1, 2, 3, 0, 4, 5, 6]) A ![m₀, m₁, m₂, p₀, p₁, p₂]
  have hS₃ : ∀ a, a ∈ S₃ ↔ a ∈ A ∧ Q V ![m₀, m₁, m₂, a, p₀, p₁, p₂] := by
    intro a
    refine (mem_sepB _ _ _ a).trans (and_congr Iff.rfl ?_)
    show Q V (fun i ↦ (a :> ![m₀, m₁, m₂, p₀, p₁, p₂]) (![1, 2, 3, 0, 4, 5, 6] i)) ↔ _
    rw [e3]
  obtain ⟨m₃, hm₃, hmin₃⟩ := hleast S₃ (fun z hz => ((hS₃ z).mp hz).1)
    ⟨g₃, (hS₃ g₃).mpr ⟨hg₃, hgQ⟩⟩
  obtain ⟨hm₃A, hmQ⟩ := (hS₃ m₃).mp hm₃
  refine ⟨m₀, hm₀A, m₁, hm₁A, m₂, hm₂A, m₃, hm₃A, hmQ, fun b₀ hb₀ b₁ hb₁ b₂ hb₂ b₃ hb₃ hb hlex => ?_⟩
  rcases hlex with h | ⟨rfl, h | ⟨rfl, h | ⟨rfl, h⟩⟩⟩
  · exact hmin₀ b₀ ((hS₀ b₀).mpr ⟨hb₀, b₁, hb₁, b₂, hb₂, b₃, hb₃, hb⟩) h
  · exact hmin₁ b₁ ((hS₁ b₁).mpr ⟨hb₁, b₂, hb₂, b₃, hb₃, hb⟩) h
  · exact hmin₂ b₂ ((hS₂ b₂).mpr ⟨hb₂, b₃, hb₃, hb⟩) h
  · exact hmin₃ b₃ ((hS₃ b₃).mpr ⟨hb₃, hb⟩) h

omit [Nonempty V] hV in
theorem lex4_tri {A lt : V}
    (htot : ∀ x, x ∈ A → ∀ y, y ∈ A → Pr lt x y ∨ (x = y ∨ Pr lt y x))
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : V} (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (ha₃ : a₃ ∈ A)
    (hb₀ : b₀ ∈ A) (hb₁ : b₁ ∈ A) (hb₂ : b₂ ∈ A) (hb₃ : b₃ ∈ A) :
    Lex4 lt a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ ∨ ((a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃) ∨
      Lex4 lt b₀ b₁ b₂ b₃ a₀ a₁ a₂ a₃) := by
  rcases htot a₀ ha₀ b₀ hb₀ with h | rfl | h
  · exact Or.inl (Or.inl h)
  · rcases htot a₁ ha₁ b₁ hb₁ with h | rfl | h
    · exact Or.inl (Or.inr ⟨rfl, Or.inl h⟩)
    · rcases htot a₂ ha₂ b₂ hb₂ with h | rfl | h
      · exact Or.inl (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inl h⟩⟩)
      · rcases htot a₃ ha₃ b₃ hb₃ with h | rfl | h
        · exact Or.inl (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩⟩)
        · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inl h⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

end lex

section order

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- `x` appears first at stage `β`. -/
def RkL (β x : V) : Prop :=
  Ord β ∧ (InDef (Lev β) (LtS β) x ∧ ∀ β', β' ∈ β → ¬InDef (Lev β') (LtS β') x)

/-- **The order of the constructible sets**: by the stage at which they appear, then the level
itself first, then by least definitions. -/
def LtL (x x' : V) : Prop :=
  ∃ β₁ β₂ : V, RkL β₁ x ∧ (RkL β₂ x' ∧
    (β₁ ∈ β₂ ∨ (β₁ = β₂ ∧ SameLess (Lev β₁) (LtS β₁) x x')))

/-- The order is total on the level at `γ`, and every set of members of the level that has a
member has a least member. -/
def WOL (γ : V) : Prop :=
  (∀ x, x ∈ Lev γ → ∀ y, y ∈ Lev γ → LtL x y ∨ (x = y ∨ LtL y x)) ∧
  ∀ Z : V, (∀ z, z ∈ Z → z ∈ Lev γ) → (∃ z, z ∈ Z) → ∃ m, m ∈ Z ∧ ∀ z, z ∈ Z → ¬LtL z m

theorem inDef_mem {β x : V} (hβ : Ord β) (h : InDef (Lev β) (LtS β) x) : x ∈ Lev (sc β) :=
  (mem_lev (ord_sc hβ)).mpr ⟨β, self_mem_sc β, h⟩

theorem rkAt_lev {F δ β x : V} (hδ : Ord δ) (hF : IsHier F δ) (hβ : β ∈ sc δ) :
    RkAt F β x ↔ RkL β x := by
  have hO := ord_mem (ord_sc hδ) hβ
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hO, (inDefAt_lev hδ hF hβ).mp h1, fun β' hβ' h =>
      h2 β' hβ' ((inDefAt_lev hδ hF ((ord_sc hδ).1 β hβ β' hβ')).mpr h)⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨(inDefAt_lev hδ hF hβ).mpr h1, fun β' hβ' h =>
      h2 β' hβ' ((inDefAt_lev hδ hF ((ord_sc hδ).1 β hβ β' hβ')).mp h)⟩

theorem rkL_unique {β β' x : V} (h : RkL β x) (h' : RkL β' x) : β = β' := by
  rcases ord_tri h.1 h'.1 with e | e | e
  · exact absurd h.2.1 (h'.2.2 β e)
  · exact e
  · exact absurd h'.2.1 (h.2.2 β' e)

theorem rkL_mem {β γ x : V} (h : RkL β x) (hγ : Ord γ) : x ∈ Lev γ ↔ β ∈ γ := by
  constructor
  · intro hx
    obtain ⟨β', hβ', hin⟩ := (mem_lev hγ).mp hx
    rcases ord_tri h.1 hγ with e | e | e
    · exact e
    · rw [← e] at hβ'
      exact absurd hin (h.2.2 β' hβ')
    · exact absurd hin (h.2.2 β' (h.1.1 γ e β' hβ'))
  · intro hβ
    exact (mem_lev hγ).mpr ⟨β, hβ, h.2.1⟩

theorem rkL_exists {γ x : V} (hγ : Ord γ) (hx : x ∈ Lev γ) : ∃ β, β ∈ γ ∧ RkL β x := by
  obtain ⟨F, hF⟩ := exists_hier hγ
  let Z : V := sepB (k := 2) (inDefAtB.comp ![1, 0, 2]) γ ![F, x]
  have hZ : ∀ β, β ∈ Z ↔ β ∈ γ ∧ InDefAt F β x := fun β => mem_sepB _ _ _ β
  obtain ⟨β₀, hβ₀, hin⟩ := (mem_lev hγ).mp hx
  have hsc : ∀ β, β ∈ γ → β ∈ sc γ := fun β h => mem_sc.mpr (Or.inr h)
  obtain ⟨β, hβZ, hmin⟩ := ord_least Z (fun z hz => ord_mem hγ ((hZ z).mp hz).1)
    ⟨β₀, (hZ β₀).mpr ⟨hβ₀, (inDefAt_lev hγ hF (hsc β₀ hβ₀)).mpr hin⟩⟩
  obtain ⟨hβ, hβin⟩ := (hZ β).mp hβZ
  refine ⟨β, hβ, ord_mem hγ hβ, (inDefAt_lev hγ hF (hsc β hβ)).mp hβin, fun β' hβ' h => ?_⟩
  have hβ'γ := hγ.1 β hβ β' hβ'
  rcases hmin β' ((hZ β').mpr ⟨hβ'γ, (inDefAt_lev hγ hF (hsc β' hβ'γ)).mpr h⟩) with e | e
  · rw [e] at hβ'
    exact mem_irrefl β' hβ'
  · exact mem_asymm e hβ'

theorem rkL_lev {ρ : V} (hρ : Ord ρ) : RkL ρ (Lev ρ) :=
  ⟨hρ, Or.inl rfl, fun β' hβ' h => by
    have h1 := inDef_mem (ord_mem hρ hβ') h
    have h2 : Lev ρ ∈ Lev ρ := lev_sub_of_le (ord_sc (ord_mem hρ hβ')) hρ
      (ord_sc_le (ord_mem hρ hβ') hρ hβ') _ h1
    exact mem_irrefl _ h2⟩

theorem keyLess_lev {F δ γ x x' : V} (hδ : Ord δ) (hF : IsHier F δ) (hγ : γ ∈ sc δ) :
    KeyLess F γ x x' ↔ ∃ β₁, β₁ ∈ γ ∧ ∃ β₂, β₂ ∈ γ ∧ (RkL β₁ x ∧ (RkL β₂ x' ∧
      (β₁ ∈ β₂ ∨ (β₁ = β₂ ∧ SameLess (Lev β₁) (LtS β₁) x x')))) := by
  have hin : ∀ β, β ∈ γ → β ∈ sc δ := fun β h => (ord_sc hδ).1 γ hγ β h
  have hsame : ∀ β, β ∈ γ → (SameAt F β x x' ↔ SameLess (Lev β) (LtS β) x x') := by
    intro β hβ
    rw [sameAt_iff]
    constructor
    · rintro ⟨A, lt, hpr, h⟩
      obtain ⟨rfl, rfl⟩ := hier_lev_eq hδ hF (hin β hβ) hpr
      exact h
    · intro h
      exact ⟨_, _, hier_lev hδ hF (hin β hβ), h⟩
  constructor
  · rintro ⟨β₁, h₁, β₂, h₂, r₁, r₂, h⟩
    refine ⟨β₁, h₁, β₂, h₂, (rkAt_lev hδ hF (hin β₁ h₁)).mp r₁,
      (rkAt_lev hδ hF (hin β₂ h₂)).mp r₂, ?_⟩
    rcases h with h | ⟨e, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, (hsame β₁ h₁).mp h⟩
  · rintro ⟨β₁, h₁, β₂, h₂, r₁, r₂, h⟩
    refine ⟨β₁, h₁, β₂, h₂, (rkAt_lev hδ hF (hin β₁ h₁)).mpr r₁,
      (rkAt_lev hδ hF (hin β₂ h₂)).mpr r₂, ?_⟩
    rcases h with h | ⟨e, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, (hsame β₁ h₁).mpr h⟩

/-- **The order of a level** is the order of the constructible sets on that level. -/
theorem lts_iff {γ x x' : V} (hγ : Ord γ) :
    Pr (LtS γ) x x' ↔ x ∈ Lev γ ∧ (x' ∈ Lev γ ∧ LtL x x') := by
  obtain ⟨F, hF⟩ := exists_hier hγ
  obtain ⟨A, lt, hpr, -, -, hc, hd⟩ := hier_at hF (self_mem_sc γ)
  obtain ⟨rfl, rfl⟩ := hier_lev_eq hγ hF (self_mem_sc γ) hpr
  constructor
  · rintro ⟨q, hq, hop⟩
    obtain ⟨a, ha, a', ha', hop'⟩ := hc q hq
    obtain ⟨e₁, e₂⟩ := op_inj hop hop'
    have hx : x ∈ Lev γ := by rw [e₁]; exact ha
    have hx' : x' ∈ Lev γ := by rw [e₂]; exact ha'
    obtain ⟨β₁, -, β₂, -, r₁, r₂, h⟩ :=
      (keyLess_lev hγ hF (self_mem_sc γ)).mp ((hd x hx x' hx').mp ⟨q, hq, hop⟩)
    exact ⟨hx, hx', β₁, β₂, r₁, r₂, h⟩
  · rintro ⟨hx, hx', β₁, β₂, r₁, r₂, h⟩
    exact (hd x hx x' hx').mpr ((keyLess_lev hγ hF (self_mem_sc γ)).mpr
      ⟨β₁, (rkL_mem r₁ hγ).mp hx, β₂, (rkL_mem r₂ hγ).mp hx', r₁, r₂, h⟩)

theorem wol_tot {ρ : V} (hρ : Ord ρ) (h : WOL ρ) :
    ∀ x, x ∈ Lev ρ → ∀ y, y ∈ Lev ρ → Pr (LtS ρ) x y ∨ (x = y ∨ Pr (LtS ρ) y x) := by
  intro x hx y hy
  rcases h.1 x hx y hy with h | h | h
  · exact Or.inl ((lts_iff hρ).mpr ⟨hx, hy, h⟩)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((lts_iff hρ).mpr ⟨hy, hx, h⟩))

theorem wol_least {ρ : V} (hρ : Ord ρ) (h : WOL ρ) :
    ∀ Z : V, (∀ z, z ∈ Z → z ∈ Lev ρ) → (∃ z, z ∈ Z) →
      ∃ m, m ∈ Z ∧ ∀ z, z ∈ Z → ¬Pr (LtS ρ) z m := by
  intro Z hZ hne
  obtain ⟨m, hm, hmin⟩ := h.2 Z hZ hne
  exact ⟨m, hm, fun z hz hp => hmin z hz ((lts_iff hρ).mp hp).2.2⟩

/-- A set that appears over a well-ordered level and is not the level has a least definition. -/
theorem leastD_exists {ρ x : V} (hρ : Ord ρ) (hw : WOL ρ) (hin : InDef (Lev ρ) (LtS ρ) x)
    (hne : x ≠ Lev ρ) : ∃ s, s ∈ Lev ρ ∧ ∃ y₁, y₁ ∈ Lev ρ ∧ ∃ y₂, y₂ ∈ Lev ρ ∧
      ∃ y₃, y₃ ∈ Lev ρ ∧ LeastD (Lev ρ) (LtS ρ) s y₁ y₂ y₃ x := by
  rcases hin with e | hex
  · exact absurd e hne
  · obtain ⟨a₀, h₀, a₁, h₁, a₂, h₂, a₃, h₃, hQ, hmin⟩ :=
      lex4_min defOfB (A := Lev ρ) (lt := LtS ρ) (Lev ρ) (LtS ρ) x (wol_least hρ hw) hex
    exact ⟨a₀, h₀, a₁, h₁, a₂, h₂, a₃, h₃, hQ, hmin⟩

theorem leastD_unique {ρ x s y₁ y₂ y₃ s' y₁' y₂' y₃' : V} (hρ : Ord ρ) (hw : WOL ρ)
    (hs : s ∈ Lev ρ) (h₁ : y₁ ∈ Lev ρ) (h₂ : y₂ ∈ Lev ρ) (h₃ : y₃ ∈ Lev ρ)
    (hs' : s' ∈ Lev ρ) (h₁' : y₁' ∈ Lev ρ) (h₂' : y₂' ∈ Lev ρ) (h₃' : y₃' ∈ Lev ρ)
    (h : LeastD (Lev ρ) (LtS ρ) s y₁ y₂ y₃ x) (h' : LeastD (Lev ρ) (LtS ρ) s' y₁' y₂' y₃' x) :
    s = s' ∧ y₁ = y₁' ∧ y₂ = y₂' ∧ y₃ = y₃' := by
  rcases lex4_tri (wol_tot hρ hw) hs h₁ h₂ h₃ hs' h₁' h₂' h₃' with hl | he | hl
  · exact absurd hl (h'.2 s hs y₁ h₁ y₂ h₂ y₃ h₃ h.1)
  · exact he
  · exact absurd hl (h.2 s' hs' y₁' h₁' y₂' h₂' y₃' h₃' h'.1)

theorem wol_step {γ : V} (hγ : Ord γ) (ih : ∀ β, β ∈ γ → WOL β) : WOL γ := by
  obtain ⟨F, hF⟩ := exists_hier hγ
  have hsc : ∀ β, β ∈ γ → β ∈ sc γ := fun β h => mem_sc.mpr (Or.inr h)
  refine ⟨fun x hx y hy => ?_, fun Z hZ hne => ?_⟩
  · obtain ⟨β₁, hβ₁, r₁⟩ := rkL_exists hγ hx
    obtain ⟨β₂, hβ₂, r₂'⟩ := rkL_exists hγ hy
    rcases ord_tri r₁.1 r₂'.1 with h | h | h
    · exact Or.inl ⟨β₁, β₂, r₁, r₂', Or.inl h⟩
    · have r₂ : RkL β₁ y := by rw [h]; exact r₂'
      have hw := ih β₁ hβ₁
      by_cases ex : x = Lev β₁
      · by_cases ey : y = Lev β₁
        · exact Or.inr (Or.inl (ex.trans ey.symm))
        · exact Or.inl ⟨β₁, β₁, r₁, r₂, Or.inr ⟨rfl, Or.inl ⟨ex, ey⟩⟩⟩
      · by_cases ey : y = Lev β₁
        · exact Or.inr (Or.inr ⟨β₁, β₁, r₂, r₁, Or.inr ⟨rfl, Or.inl ⟨ey, ex⟩⟩⟩)
        · obtain ⟨s, hs, y₁, h₁, y₂, h₂, y₃, h₃, hL⟩ := leastD_exists r₁.1 hw r₁.2.1 ex
          obtain ⟨s', hs', y₁', h₁', y₂', h₂', y₃', h₃', hL'⟩ :=
            leastD_exists r₁.1 hw r₂.2.1 ey
          rcases lex4_tri (wol_tot r₁.1 hw) hs h₁ h₂ h₃ hs' h₁' h₂' h₃' with hl | he | hl
          · exact Or.inl ⟨β₁, β₁, r₁, r₂, Or.inr ⟨rfl, Or.inr ⟨ex, ey, s, hs, y₁, h₁, y₂, h₂,
              y₃, h₃, s', hs', y₁', h₁', y₂', h₂', y₃', h₃', hL, hL', hl⟩⟩⟩
          · obtain ⟨rfl, rfl, rfl, rfl⟩ := he
            exact Or.inr (Or.inl (mem_ext (isD_ext hL.1 hL'.1)))
          · exact Or.inr (Or.inr ⟨β₁, β₁, r₂, r₁, Or.inr ⟨rfl, Or.inr ⟨ey, ex, s', hs', y₁', h₁',
              y₂', h₂', y₃', h₃', s, hs, y₁, h₁, y₂, h₂, y₃, h₃, hL', hL, hl⟩⟩⟩)
    · exact Or.inr (Or.inr ⟨β₂, β₁, r₂', r₁, Or.inl h⟩)
  · let R : V := sepB (k := 2) (BDef.bex 1 (rkAtB.comp ![3, 1, 0])) γ ![Z, F]
    have hR : ∀ β, β ∈ R ↔ β ∈ γ ∧ ∃ z, z ∈ Z ∧ RkAt F β z := fun β => mem_sepB _ _ _ β
    have hrk : ∀ β, β ∈ γ → ∀ z, (RkAt F β z ↔ RkL β z) :=
      fun β hβ z => rkAt_lev hγ hF (hsc β hβ)
    obtain ⟨z₁, hz₁⟩ := hne
    obtain ⟨β₁, hβ₁, r₁⟩ := rkL_exists hγ (hZ z₁ hz₁)
    obtain ⟨ρ, hρR, hmin⟩ := ord_least R (fun z hz => ord_mem hγ ((hR z).mp hz).1)
      ⟨β₁, (hR β₁).mpr ⟨hβ₁, z₁, hz₁, (hrk β₁ hβ₁ z₁).mpr r₁⟩⟩
    obtain ⟨hρ, z₂, hz₂, r₂'⟩ := (hR ρ).mp hρR
    have r₂ : RkL ρ z₂ := (hrk ρ hρ z₂).mp r₂'
    have hρO : Ord ρ := ord_mem hγ hρ
    have hlow : ∀ z, z ∈ Z → ∀ β, RkL β z → ¬β ∈ ρ := by
      intro z hz β r hβ
      have hβγ := hγ.1 ρ hρ β hβ
      rcases hmin β ((hR β).mpr ⟨hβγ, z, hz, (hrk β hβγ z).mpr r⟩) with e | e
      · rw [e] at hβ
        exact mem_irrefl β hβ
      · exact mem_asymm e hβ
    by_cases hL : Lev ρ ∈ Z
    · refine ⟨Lev ρ, hL, fun z hz hlt => ?_⟩
      obtain ⟨b₁, b₂, s₁, s₂, h⟩ := hlt
      have e := rkL_unique s₂ (rkL_lev hρO)
      rcases h with h | ⟨e', h⟩
      · rw [e] at h
        exact hlow z hz b₁ s₁ h
      · rw [e', e] at h
        rcases h with ⟨-, hn⟩ | ⟨-, hn, -⟩
        · exact hn rfl
        · exact hn rfl
    · let Z₀ : V := sepB (k := 2) (rkAtB.comp ![1, 2, 0]) Z ![F, ρ]
      have hZ₀ : ∀ z, z ∈ Z₀ ↔ z ∈ Z ∧ RkAt F ρ z := fun z => mem_sepB _ _ _ z
      have hw := ih ρ hρ
      have hne₂ : z₂ ≠ Lev ρ := fun e => hL (e ▸ hz₂)
      obtain ⟨s, hs, y₁, h₁, y₂, h₂, y₃, h₃, hLD⟩ := leastD_exists hρO hw r₂.2.1 hne₂
      obtain ⟨a₀, h₀, a₁, ha₁, a₂, ha₂, a₃, ha₃, ⟨z₀, hz₀, hLD₀⟩, hmin₀⟩ :=
        lex4_min keyOfB (A := Lev ρ) (lt := LtS ρ) (Lev ρ) (LtS ρ) Z₀ (wol_least hρO hw)
          ⟨s, hs, y₁, h₁, y₂, h₂, y₃, h₃, z₂, (hZ₀ z₂).mpr ⟨hz₂, r₂'⟩, hLD⟩
      obtain ⟨hz₀Z, r₀'⟩ := (hZ₀ z₀).mp hz₀
      have r₀ : RkL ρ z₀ := (hrk ρ hρ z₀).mp r₀'
      refine ⟨z₀, hz₀Z, fun z hz hlt => ?_⟩
      obtain ⟨b₁, b₂, s₁, s₂, h⟩ := hlt
      have e := rkL_unique s₂ r₀
      rcases h with h | ⟨e', h⟩
      · rw [e] at h
        exact hlow z hz b₁ s₁ h
      · have s₁' : RkL ρ z := by rw [← e, ← e']; exact s₁
        rw [e', e] at h
        rcases h with ⟨ez, -⟩ | ⟨-, -, t, ht, u₁, hu₁, u₂, hu₂, u₃, hu₃, t', ht', u₁', hu₁', u₂',
          hu₂', u₃', hu₃', hD, hD', hlex⟩
        · exact hL (ez ▸ hz)
        · obtain ⟨e0, e1, e2, e3⟩ :=
            leastD_unique hρO hw ht' hu₁' hu₂' hu₃' h₀ ha₁ ha₂ ha₃ hD' hLD₀
          rw [e0, e1, e2, e3] at hlex
          exact hmin₀ t ht u₁ hu₁ u₂ hu₂ u₃ hu₃
            ⟨z, (hZ₀ z).mpr ⟨hz, (hrk ρ hρ z).mpr s₁'⟩, hD⟩ hlex

/-- **Every level is well-ordered** by the order of the constructible sets. -/
theorem wol {γ : V} (hγ : Ord γ) : WOL γ := by
  by_contra hcon
  obtain ⟨F, hF⟩ := exists_hier hγ
  let P : V := ℘ (Lev γ)
  let Z : V := sepB (k := 2) (notWOAtB.comp ![0, 1, 2]) (sc γ) ![F, P]
  have hZ : ∀ β, β ∈ Z ↔ β ∈ sc γ ∧ NotWOAt β F P := fun β => mem_sepB _ _ _ β
  have key : ∀ β, β ∈ sc γ → (NotWOAt β F P ↔ ¬WOL β) := by
    intro β hβ
    have hβO := ord_mem (ord_sc hγ) hβ
    have hsub : ∀ x, x ∈ Lev β → x ∈ Lev γ := lev_sub_of_le hβO hγ (mem_sc.mp hβ)
    have hw : WOr (Lev β) (LtS β) P ↔ WOL β := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun x hx y hy => ?_, fun Z' hZ' hne => ?_⟩
        · rcases h1 x hx y hy with h | h | h
          · exact Or.inl ((lts_iff hβO).mp h).2.2
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ((lts_iff hβO).mp h).2.2)
        · obtain ⟨z, hz⟩ := hne
          obtain ⟨m, hm, hmin⟩ := h2 Z' (mem_power_iff.mpr fun z hz => hsub z (hZ' z hz)) hZ'
            ⟨z, hz, not_false⟩
          exact ⟨m, hm, fun z hz hlt => hmin z hz ((lts_iff hβO).mpr ⟨hZ' z hz, hZ' m hm, hlt⟩)⟩
      · intro h
        exact ⟨wol_tot hβO h, fun Z' _ hZ' ⟨z, hz, _⟩ => wol_least hβO h Z' hZ' ⟨z, hz⟩⟩
    rw [← hw]
    constructor
    · intro h hWO
      obtain ⟨A, lt, hpr, hn⟩ := exAt_iff.mp h
      obtain ⟨rfl, rfl⟩ := hier_lev_eq hγ hF hβ hpr
      exact hn hWO
    · intro h
      exact exAt_iff.mpr ⟨_, _, hier_lev hγ hF hβ, h⟩
  have hne : ∃ β, β ∈ Z := ⟨γ, (hZ γ).mpr ⟨self_mem_sc γ, (key γ (self_mem_sc γ)).mpr hcon⟩⟩
  obtain ⟨β, hβZ, hmin⟩ := ord_least Z (fun z hz => ord_mem (ord_sc hγ) ((hZ z).mp hz).1) hne
  obtain ⟨hβ, hn⟩ := (hZ β).mp hβZ
  have hβO := ord_mem (ord_sc hγ) hβ
  refine (key β hβ).mp hn (wol_step hβO fun β' hβ' => ?_)
  by_contra hn'
  have hβ'sc : β' ∈ sc γ := (ord_sc hγ).1 β hβ β' hβ'
  rcases hmin β' ((hZ β').mpr ⟨hβ'sc, (key β' hβ'sc).mpr hn'⟩) with e | e
  · rw [e] at hβ'
    exact mem_irrefl β' hβ'
  · exact mem_asymm e hβ'

theorem ltL_tri {γ x y : V} (hγ : Ord γ) (hx : x ∈ Lev γ) (hy : y ∈ Lev γ) :
    LtL x y ∨ (x = y ∨ LtL y x) := (wol hγ).1 x hx y hy

theorem ltL_least {γ : V} (hγ : Ord γ) (Z : V) (hZ : ∀ z, z ∈ Z → z ∈ Lev γ)
    (hne : ∃ z, z ∈ Z) : ∃ m, m ∈ Z ∧ ∀ z, z ∈ Z → ¬LtL z m := (wol hγ).2 Z hZ hne

end order

end MH

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.wol
