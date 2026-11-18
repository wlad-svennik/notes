import MHBasics

set_option autoImplicit false

/-!
# Recursion along an ordinal, and limit ordinals

Inside a model `V` of `𝗠`.

* `IsAtt G p f β`: `f` is a function on the ordinal `β` such that `G (γ, f, f γ, p)` for every
  `γ ∈ β`. Here `G` is a relation with a bounded definition which depends on `f` only through
  its values below `γ` (`hloc`) and determines the value (`huniq`).
* `att_agree`: two such functions agree where both are defined.
* `ord_rec`: if every function of this kind on a `β ≤ δ` can be extended by a value in a given
  set `C`, there is one on `δ + 1`.

Inside a model of `𝗠𝗛`:

* `exists_lim`: above every ordinal there is a limit ordinal. The ordinal is the collapse of
  the given ordinal followed by a copy of ω.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section rec

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- `f` is a function on `β` with `G (γ, f, f γ, p)` for every `γ ∈ β`. -/
def IsAtt {k : ℕ} (G : MRel (k + 3)) (p : Fin k → V) (f β : V) : Prop :=
  (∀ q, q ∈ f → ∃ γ, γ ∈ β ∧ ∃ u, u ∈ q ∧ ∃ y, y ∈ u ∧ IsOp q γ y) ∧
  (∀ γ, γ ∈ β → ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ y, y ∈ u ∧ (IsOp q γ y ∧ G V (γ :> f :> y :> p))) ∧
  (∀ q, q ∈ f → ∀ q', q' ∈ f → ∀ γ, γ ∈ β → ∀ u, u ∈ q → ∀ y, y ∈ u → ∀ u', u' ∈ q' →
    ∀ y', y' ∈ u' → IsOp q γ y → IsOp q' γ y' → y = y')

end rec

/-- `IsAtt` is bounded. The variables are `f`, `β` and the parameters. -/
def isAttB {k : ℕ} {G : MRel (k + 3)} (dG : BDef G) :
    BDef (k := k + 2) (fun V _ v ↦ IsAtt G (fun i ↦ v i.succ.succ) (v 0) (v 1)) :=
  ((BDef.ball 0 (BDef.bex 2 (BDef.bex 1 (BDef.bex 0 (isOpB.comp ![3, 2, 0]))))).and
    ((BDef.ball 1 (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and
      (dG.comp (fun i ↦ Fin.cases 3 (fun j ↦ Fin.cases 4 (fun l ↦ Fin.cases 0
        (fun m ↦ m.succ.succ.succ.succ.succ.succ) l) j) i))))))).and
    (BDef.ball 0 (BDef.ball 1 (BDef.ball 3 (BDef.ball 2 (BDef.ball 0 (BDef.ball 3 (BDef.ball 0
      ((isOpB.comp ![6, 4, 2]).imp ((isOpB.comp ![5, 4, 0]).imp (BDef.eq 2 0)))))))))))).congr
    fun V _ v => by
      refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
      refine forall_congr' fun γ => imp_congr Iff.rfl (exists_congr fun q => and_congr Iff.rfl
        (exists_congr fun u => and_congr Iff.rfl (exists_congr fun y => and_congr Iff.rfl
          (and_congr Iff.rfl ?_))))
      have e : (fun i ↦ (y :> u :> q :> γ :> v)
          ((fun i ↦ Fin.cases 3 (fun j ↦ Fin.cases 4 (fun l ↦ Fin.cases 0
            (fun m ↦ m.succ.succ.succ.succ.succ.succ) l) j) i : Fin (k + 3) → Fin (k + 6)) i)) =
          (γ :> v 0 :> y :> fun i ↦ v i.succ.succ) := by
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          cases j using Fin.cases with
          | zero => rfl
          | succ l =>
            cases l using Fin.cases with
            | zero => rfl
            | succ m => rfl
      show G V (fun i ↦ (y :> u :> q :> γ :> v) _) ↔ _
      rw [e]

section rec

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]
variable {k : ℕ} {G : MRel (k + 3)} {p : Fin k → V}

theorem att_dom {f β γ y : V} (hf : IsAtt G p f β) (h : Pr f γ y) : γ ∈ β := by
  obtain ⟨q, hq, hop⟩ := h
  obtain ⟨γ', hγ', u, -, y', -, hop'⟩ := hf.1 q hq
  exact (op_inj hop hop').1 ▸ hγ'

theorem att_fun {f β γ y y' : V} (hf : IsAtt G p f β) (h : Pr f γ y) (h' : Pr f γ y') :
    y = y' := by
  have hγ := att_dom hf h
  obtain ⟨q, hq, hop⟩ := h
  obtain ⟨q', hq', hop'⟩ := h'
  obtain ⟨u, hu, hyu⟩ := pr_snd_mem hop
  obtain ⟨u', hu', hyu'⟩ := pr_snd_mem hop'
  exact hf.2.2 q hq q' hq' γ hγ u hu y hyu u' hu' y' hyu' hop hop'

theorem att_total {f β γ : V} (hf : IsAtt G p f β) (hγ : γ ∈ β) :
    ∃ y, Pr f γ y ∧ G V (γ :> f :> y :> p) := by
  obtain ⟨q, hq, u, -, y, -, hop, hG⟩ := hf.2.1 γ hγ
  exact ⟨y, ⟨q, hq, hop⟩, hG⟩

theorem att_G {f β γ y : V} (hf : IsAtt G p f β) (h : Pr f γ y) : G V (γ :> f :> y :> p) := by
  obtain ⟨y', hy', hG⟩ := att_total hf (att_dom hf h)
  rw [att_fun hf h hy']
  exact hG

variable (hloc : ∀ γ f f' y : V, Ord γ → (∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y') →
    G V (γ :> f :> y :> p) → G V (γ :> f' :> y :> p))
  (huniq : ∀ γ f y y' : V, G V (γ :> f :> y :> p) → G V (γ :> f :> y' :> p) → y = y')

include hloc huniq in
/-- **Two attempts agree where both are defined.** -/
theorem att_agree {f f' β β' : V} (hβ : Ord β) (hβ' : Ord β') (hf : IsAtt G p f β)
    (hf' : IsAtt G p f' β') :
    ∀ γ, γ ∈ β → γ ∈ β' → ∀ y, Pr f γ y → Pr f' γ y := by
  by_contra hcon
  let Z : V := sepB (k := 3) ((BDef.mem 0 3).and (BDef.bex 1 (BDef.bex 0 (BDef.bex 0
    ((isOpB.comp ![2, 3, 0]).and (prB.comp ![5, 3, 0]).not))))) β ![f, f', β']
  have hZ : ∀ γ, γ ∈ Z ↔ γ ∈ β ∧ γ ∈ β' ∧ ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ y, y ∈ u ∧
      (IsOp q γ y ∧ ¬Pr f' γ y) := fun γ => mem_sepB _ _ _ γ
  have hne : ∃ γ, γ ∈ Z := by
    by_contra h
    refine hcon fun γ hγ hγ' y hy => ?_
    by_contra hn
    obtain ⟨q, hq, hop⟩ := hy
    obtain ⟨u, hu, hyu⟩ := pr_snd_mem hop
    exact h ⟨γ, (hZ γ).mpr ⟨hγ, hγ', q, hq, u, hu, y, hyu, hop, hn⟩⟩
  obtain ⟨γ, hγZ, hmin⟩ := ord_least Z (fun z hz => ord_mem hβ ((hZ z).mp hz).1) hne
  obtain ⟨hγ, hγ', q, hq, u, -, y, -, hop, hn⟩ := (hZ γ).mp hγZ
  have hy : Pr f γ y := ⟨q, hq, hop⟩
  have hbelow : ∀ γ₁, γ₁ ∈ γ → ∀ y₁, Pr f γ₁ y₁ ↔ Pr f' γ₁ y₁ := by
    intro γ₁ hγ₁ y₁
    have h1 : γ₁ ∈ β := hβ.1 γ hγ γ₁ hγ₁
    have h1' : γ₁ ∈ β' := hβ'.1 γ hγ' γ₁ hγ₁
    constructor
    · intro h
      by_contra hn'
      obtain ⟨q₁, hq₁, hop₁⟩ := h
      obtain ⟨u₁, hu₁, hyu₁⟩ := pr_snd_mem hop₁
      rcases hmin γ₁ ((hZ γ₁).mpr ⟨h1, h1', q₁, hq₁, u₁, hu₁, y₁, hyu₁, hop₁, hn'⟩) with e | e
      · exact mem_irrefl γ₁ (e ▸ hγ₁)
      · exact mem_asymm e hγ₁
    · intro h
      obtain ⟨y₂, hy₂, -⟩ := att_total hf h1
      have : Pr f' γ₁ y₂ := by
        by_contra hn'
        obtain ⟨q₁, hq₁, hop₁⟩ := hy₂
        obtain ⟨u₁, hu₁, hyu₁⟩ := pr_snd_mem hop₁
        rcases hmin γ₁ ((hZ γ₁).mpr ⟨h1, h1', q₁, hq₁, u₁, hu₁, y₂, hyu₁, hop₁, hn'⟩) with e | e
        · exact mem_irrefl γ₁ (e ▸ hγ₁)
        · exact mem_asymm e hγ₁
      rw [att_fun hf' h this]
      exact hy₂
  obtain ⟨y', hy', hG'⟩ := att_total hf' hγ'
  have hG : G V (γ :> f' :> y :> p) := hloc γ f f' y (ord_mem hβ hγ) hbelow (att_G hf hy)
  exact hn (huniq γ f' y y' hG hG' ▸ hy')

end rec

section rec2

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]
variable {k : ℕ} {G : MRel (k + 3)} {p : Fin k → V}

theorem att_agree_iff
    (hloc : ∀ γ f f' y : V, Ord γ → (∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y') →
      G V (γ :> f :> y :> p) → G V (γ :> f' :> y :> p))
    (huniq : ∀ γ f y y' : V, G V (γ :> f :> y :> p) → G V (γ :> f :> y' :> p) → y = y')
    {f f' β β' : V} (hβ : Ord β) (hβ' : Ord β') (hf : IsAtt G p f β) (hf' : IsAtt G p f' β')
    {γ : V} (hγ : γ ∈ β) (hγ' : γ ∈ β') (y : V) : Pr f γ y ↔ Pr f' γ y :=
  ⟨att_agree hloc huniq hβ hβ' hf hf' γ hγ hγ' y, att_agree hloc huniq hβ' hβ hf' hf γ hγ' hγ y⟩

/-- **Recursion along an ordinal.** -/
theorem ord_rec (dG : BDef G)
    (hloc : ∀ γ f f' y : V, Ord γ → (∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y') →
      G V (γ :> f :> y :> p) → G V (γ :> f' :> y :> p))
    (huniq : ∀ γ f y y' : V, G V (γ :> f :> y :> p) → G V (γ :> f :> y' :> p) → y = y')
    (δ C : V) (hδ : Ord δ)
    (hstep : ∀ β, β ∈ sc δ → ∀ f, f ∈ ℘ (prodS (sc δ) C) → IsAtt G p f β →
      ∃ y, y ∈ C ∧ G V (β :> f :> y :> p)) :
    ∃ F, IsAtt G p F (sc δ) := by
  let PC : V := ℘ (prodS (sc δ) C)
  have hOsc : Ord (sc δ) := ord_sc hδ
  have hOsc2 : Ord (sc (sc δ)) := ord_sc hOsc
  have claim : ∀ β, β ∈ sc (sc δ) → ∃ f, f ∈ PC ∧ IsAtt G p f β := by
    by_contra hcon
    let Z : V := sepB (k := k + 1) ((BDef.bex 1 ((isAttB dG).comp
      (fun i ↦ Fin.cases 0 (fun j ↦ Fin.cases 1 (fun l ↦ l.succ.succ.succ) j) i))).not)
      (sc (sc δ)) (PC :> p)
    have hZ : ∀ β, β ∈ Z ↔ β ∈ sc (sc δ) ∧ ¬∃ f, f ∈ PC ∧ IsAtt G p f β := by
      intro β
      refine (mem_sepB _ _ _ β).trans (and_congr Iff.rfl (not_congr (exists_congr fun f =>
        and_congr Iff.rfl ?_)))
      exact Iff.rfl
    have hne : ∃ β, β ∈ Z := by
      by_contra h
      exact hcon fun β hβ => by
        by_contra hno
        exact h ⟨β, (hZ β).mpr ⟨hβ, hno⟩⟩
    obtain ⟨β, hβZ, hmin⟩ := ord_least Z (fun z hz => ord_mem hOsc2 ((hZ z).mp hz).1) hne
    obtain ⟨hβ2, hnoβ⟩ := (hZ β).mp hβZ
    have hβO : Ord β := ord_mem hOsc2 hβ2
    have hβsub : ∀ γ, γ ∈ β → γ ∈ sc δ := fun γ hγ => by
      rcases mem_sc.mp hβ2 with rfl | h
      · exact hγ
      · exact hOsc.1 β h γ hγ
    have hbelow : ∀ γ, γ ∈ β → ∃ f, f ∈ PC ∧ IsAtt G p f γ := fun γ hγ => by
      by_contra hno
      rcases hmin γ ((hZ γ).mpr ⟨mem_sc.mpr (Or.inr (hβsub γ hγ)), hno⟩) with e | e
      · exact mem_irrefl γ (e ▸ hγ)
      · exact mem_asymm e hγ
    let f : V := sepB (k := k + 3) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
      (BDef.bex 5 (((isAttB dG).comp (fun i ↦ Fin.cases 0 (fun j ↦ Fin.cases 2
        (fun l ↦ l.succ.succ.succ.succ.succ.succ.succ) j) i)).and
        (dG.comp (fun i ↦ Fin.cases 2 (fun j ↦ Fin.cases 0 (fun l ↦ Fin.cases 1
          (fun m ↦ m.succ.succ.succ.succ.succ.succ.succ) l) j) i)))))))
      (prodS (sc δ) C) (β :> C :> PC :> p)
    have hf : ∀ z, z ∈ f ↔ z ∈ prodS (sc δ) C ∧ ∃ γ, γ ∈ β ∧ ∃ y, y ∈ C ∧ (IsOp z γ y ∧
        ∃ f', f' ∈ PC ∧ (IsAtt G p f' γ ∧ G V (γ :> f' :> y :> p))) := by
      intro z
      refine (mem_sepB _ _ _ z).trans (and_congr Iff.rfl (exists_congr fun γ => and_congr Iff.rfl
        (exists_congr fun y => and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun f' =>
          and_congr Iff.rfl (and_congr Iff.rfl ?_))))))
      have e : (fun i ↦ (f' :> y :> γ :> z :> β :> C :> PC :> p)
          ((fun i ↦ Fin.cases 2 (fun j ↦ Fin.cases 0 (fun l ↦ Fin.cases 1
            (fun m ↦ m.succ.succ.succ.succ.succ.succ.succ) l) j) i :
              Fin (k + 3) → Fin (k + 7)) i)) = (γ :> f' :> y :> p) := by
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          cases j using Fin.cases with
          | zero => rfl
          | succ l =>
            cases l using Fin.cases with
            | zero => rfl
            | succ m => rfl
      show G V (fun i ↦ (f' :> y :> γ :> z :> β :> C :> PC :> p) _) ↔ _
      rw [e]
    have hfval : ∀ γ y, Pr f γ y ↔ γ ∈ β ∧ y ∈ C ∧
        ∃ f', f' ∈ PC ∧ IsAtt G p f' γ ∧ G V (γ :> f' :> y :> p) := by
      intro γ y
      rw [pr_iff, hf]
      constructor
      · rintro ⟨-, γ', hγ', y', hy', hop, f', hf'PC, hf', hG⟩
        obtain ⟨rfl, rfl⟩ := op_inj (isOp_kp γ y) hop
        exact ⟨hγ', hy', f', hf'PC, hf', hG⟩
      · rintro ⟨hγ, hy, f', hf'PC, hf', hG⟩
        exact ⟨mem_prodS.mpr ⟨γ, hβsub γ hγ, y, hy, rfl⟩, γ, hγ, y, hy, isOp_kp γ y, f',
          hf'PC, hf', hG⟩
    have hcoh : ∀ γ, γ ∈ β → ∀ f₁ f₂, IsAtt G p f₁ γ → IsAtt G p f₂ γ → ∀ y,
        G V (γ :> f₁ :> y :> p) → G V (γ :> f₂ :> y :> p) := fun γ hγ f₁ f₂ h1 h2 y hG =>
      hloc γ f₁ f₂ y (ord_mem hβO hγ) (fun γ' hγ' y' => att_agree_iff hloc huniq (ord_mem hβO hγ)
        (ord_mem hβO hγ) h1 h2 hγ' hγ' y') hG
    have hagree : ∀ γ, γ ∈ β → ∀ f', IsAtt G p f' γ → f' ∈ PC → ∀ γ', γ' ∈ γ → ∀ y',
        (Pr f' γ' y' ↔ Pr f γ' y') := by
      intro γ hγ f' hf' hf'PC γ' hγ' y'
      have hγ'β : γ' ∈ β := hβO.1 γ hγ γ' hγ'
      obtain ⟨f'', hf''PC, hf''⟩ := hbelow γ' hγ'β
      have hag : ∀ γ₂, γ₂ ∈ γ' → ∀ y₂, Pr f' γ₂ y₂ ↔ Pr f'' γ₂ y₂ := fun γ₂ hγ₂ y₂ =>
        att_agree_iff hloc huniq (ord_mem hβO hγ) (ord_mem hβO hγ'β) hf' hf''
          ((ord_mem hβO hγ).1 γ' hγ' γ₂ hγ₂) hγ₂ y₂
      constructor
      · intro h
        have hy'C : y' ∈ C := by
          have := mem_power_iff.mp hf'PC (kp γ' y') (pr_iff.mp h)
          obtain ⟨a, -, b, hb, e⟩ := mem_prodS.mp this
          rw [(kp_inj e).2]; exact hb
        exact (hfval γ' y').mpr ⟨hγ'β, hy'C, f'', hf''PC, hf'', hloc γ' f' f'' y' (ord_mem hβO hγ'β) hag (att_G hf' h)⟩
      · intro h
        obtain ⟨-, -, f₃, -, hf₃, hG₃⟩ := (hfval γ' y').mp h
        obtain ⟨ys, hys, hGs⟩ := att_total hf' hγ'
        have hG' : G V (γ' :> f' :> y' :> p) :=
          hloc γ' f'' f' y' (ord_mem hβO hγ'β) (fun γ₂ hγ₂ y₂ => (hag γ₂ hγ₂ y₂).symm)
            (hcoh γ' hγ'β f₃ f'' hf₃ hf'' y' hG₃)
        rw [huniq γ' f' y' ys hG' hGs]
        exact hys
    have hfatt : IsAtt G p f β := by
      refine ⟨fun q hq => ?_, fun γ hγ => ?_, fun q hq q' hq' γ hγ u _ y _ u' _ y' _ hop hop' => ?_⟩
      · obtain ⟨-, γ, hγ, y, -, hop, -⟩ := (hf q).mp hq
        obtain ⟨u, hu, hyu⟩ := pr_snd_mem hop
        exact ⟨γ, hγ, u, hu, y, hyu, hop⟩
      · obtain ⟨f', hf'PC, hf'⟩ := hbelow γ hγ
        obtain ⟨y, hyC, hG⟩ := hstep γ (hβsub γ hγ) f' hf'PC hf'
        have hpr : Pr f γ y := (hfval γ y).mpr ⟨hγ, hyC, f', hf'PC, hf', hG⟩
        obtain ⟨q, hq, hop⟩ := hpr
        obtain ⟨u, hu, hyu⟩ := pr_snd_mem hop
        exact ⟨q, hq, u, hu, y, hyu, hop,
          hloc γ f' f y (ord_mem hβO hγ) (hagree γ hγ f' hf' hf'PC) hG⟩
      · obtain ⟨-, -, f₁, -, hf₁, hG₁⟩ := (hfval γ y).mp ⟨q, hq, hop⟩
        obtain ⟨-, -, f₂, -, hf₂, hG₂⟩ := (hfval γ y').mp ⟨q', hq', hop'⟩
        exact huniq γ f₂ y y' (hcoh γ hγ f₁ f₂ hf₁ hf₂ y hG₁) hG₂
    exact hnoβ ⟨f, mem_power_iff.mpr (fun z hz => ((hf z).mp hz).1), hfatt⟩
  obtain ⟨F, -, hF⟩ := claim (sc δ) (self_mem_sc _)
  exact ⟨F, hF⟩

end rec2

/-! ### Limit ordinals -/

section lim

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The lexicographic order of the pairs `⟨γ, n⟩`: first `γ`, then `n`. -/
def LexR (a b : V) : Prop :=
  ∃ u, u ∈ a ∧ ∃ γ, γ ∈ u ∧ ∃ u₁, u₁ ∈ a ∧ ∃ n, n ∈ u₁ ∧ ∃ w, w ∈ b ∧ ∃ γ', γ' ∈ w ∧
    ∃ w₁, w₁ ∈ b ∧ ∃ n', n' ∈ w₁ ∧
      (IsOp a γ n ∧ (IsOp b γ' n' ∧ (γ ∈ γ' ∨ (γ = γ' ∧ n ∈ n'))))

end lim

def lexRB : BDef (k := 2) (fun V _ v ↦ LexR (v 0) (v 1)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0 (BDef.bex 5 (BDef.bex 0 (BDef.bex 7
    (BDef.bex 0 ((isOpB.comp ![8, 6, 4]).and ((isOpB.comp ![9, 2, 0]).and
      ((BDef.mem 6 2).or ((BDef.eq 6 2).and (BDef.mem 4 0))))))))))))).congr
    fun _ _ _ => Iff.rfl

section lim

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem lexR_iff {γ n γ' n' : V} :
    LexR (kp γ n) (kp γ' n') ↔ γ ∈ γ' ∨ (γ = γ' ∧ n ∈ n') := by
  constructor
  · rintro ⟨u, -, g, -, u₁, -, m, -, w, -, g', -, w₁, -, m', -, h1, h2, h3⟩
    obtain ⟨rfl, rfl⟩ := op_inj (isOp_kp γ n) h1
    obtain ⟨rfl, rfl⟩ := op_inj (isOp_kp γ' n') h2
    exact h3
  · intro h
    obtain ⟨u, hu, hγu⟩ := pr_fst_mem (isOp_kp γ n)
    obtain ⟨u₁, hu₁, hnu⟩ := pr_snd_mem (isOp_kp γ n)
    obtain ⟨w, hw, hγw⟩ := pr_fst_mem (isOp_kp γ' n')
    obtain ⟨w₁, hw₁, hnw⟩ := pr_snd_mem (isOp_kp γ' n')
    exact ⟨u, hu, γ, hγu, u₁, hu₁, n, hnu, w, hw, γ', hγw, w₁, hw₁, n', hnw, isOp_kp γ n,
      isOp_kp γ' n', h⟩

/-- **Above every ordinal there is a limit ordinal.** -/
theorem exists_lim {γ₀ : V} (h₀ : Ord γ₀) : ∃ lam : V, Lim lam ∧ γ₀ ∈ lam := by
  let S : V := sc γ₀
  have hS : Ord S := ord_sc h₀
  let u : V := prodS S (om : V)
  obtain ⟨T, hT, hcol⟩ := hc_of_models (V := V) u
  let r : V := relB (k := 0) lexRB u u ![]
  have hr : ∀ a b, Pr r a b ↔ a ∈ u ∧ b ∈ u ∧ LexR a b := fun a b => pr_relB lexRB u u ![] a b
  have hu : ∀ a, a ∈ u ↔ ∃ γ, γ ∈ S ∧ ∃ n, n ∈ (om : V) ∧ a = kp γ n := fun a => mem_prodS
  have hrk : ∀ γ n γ' n', Pr r (kp γ n) (kp γ' n') ↔ γ ∈ S ∧ n ∈ (om : V) ∧ γ' ∈ S ∧
      n' ∈ (om : V) ∧ (γ ∈ γ' ∨ (γ = γ' ∧ n ∈ n')) := by
    intro γ n γ' n'
    rw [hr, hu, hu, lexR_iff]
    constructor
    · rintro ⟨⟨g, hg, m, hm, e⟩, ⟨g', hg', m', hm', e'⟩, h⟩
      obtain ⟨rfl, rfl⟩ := kp_inj e
      obtain ⟨rfl, rfl⟩ := kp_inj e'
      exact ⟨hg, hm, hg', hm', h⟩
    · rintro ⟨hg, hm, hg', hm', h⟩
      exact ⟨⟨γ, hg, n, hm, rfl⟩, ⟨γ', hg', n', hm', rfl⟩, h⟩
  have hwf : WFon r u := by
    rintro X ⟨c₀, hc₀, -⟩ hXu
    -- least first coordinate
    let A : V := sepB (k := 2) (BDef.bex 1 (BDef.bex 3 (isOpB.comp ![1, 2, 0]))) S ![X, (om : V)]
    have hA : ∀ γ, γ ∈ A ↔ γ ∈ S ∧ ∃ a, a ∈ X ∧ ∃ n, n ∈ (om : V) ∧ IsOp a γ n :=
      fun γ => mem_sepB _ _ _ γ
    obtain ⟨g₀, hg₀, n₀, hn₀, rfl⟩ := (hu c₀).mp (hXu c₀ hc₀)
    obtain ⟨g, hgA, hgmin⟩ := ord_least A (fun z hz => ord_mem hS ((hA z).mp hz).1)
      ⟨g₀, (hA g₀).mpr ⟨hg₀, _, hc₀, n₀, hn₀, isOp_kp g₀ n₀⟩⟩
    let B : V := sepB (k := 2) (BDef.bex 1 (isOpB.comp ![0, 3, 1])) (om : V) ![X, g]
    have hB : ∀ n, n ∈ B ↔ n ∈ (om : V) ∧ ∃ a, a ∈ X ∧ IsOp a g n := fun n => mem_sepB _ _ _ n
    obtain ⟨hgS, a₁, ha₁, n₁, hn₁, hop₁⟩ := (hA g).mp hgA
    obtain ⟨n, hnB, hnmin⟩ := ord_least B (fun z hz => ord_mem ord_om ((hB z).mp hz).1)
      ⟨n₁, (hB n₁).mpr ⟨hn₁, a₁, ha₁, hop₁⟩⟩
    obtain ⟨hn, a, ha, hop⟩ := (hB n).mp hnB
    have ea : a = kp g n := isOp_iff.mp hop
    subst ea
    refine ⟨kp g n, ha, fun b hb hbr => ?_⟩
    obtain ⟨g', hg', n', hn', rfl⟩ := (hu b).mp (hXu b hb)
    rcases ((hrk g' n' g n).mp hbr).2.2.2.2 with h | ⟨rfl, h⟩
    · rcases hgmin g' ((hA g').mpr ⟨hg', _, hb, n', hn', isOp_kp g' n'⟩) with e | e
      · exact mem_irrefl g' (e ▸ h)
      · exact mem_asymm e h
    · rcases hnmin n' ((hB n').mpr ⟨hn', _, hb, isOp_kp g' n'⟩) with e | e
      · exact mem_irrefl n' (e ▸ h)
      · exact mem_asymm e h
  obtain ⟨F, hF⟩ := hcol r hwf
  -- the value of the collapse
  have hFv : ∀ a, a ∈ u → ∃ v, v ∈ T ∧ Pr F a v ∧ (∀ v', Pr F a v' → v' = v) ∧
      ∀ y, (y ∈ v ↔ ∃ a', a' ∈ u ∧ Pr r a' a ∧ Pr F a' y) := hF
  have hrtrans : ∀ a b c, Pr r a b → Pr r b c → Pr r a c := by
    intro a b c hab hbc
    obtain ⟨g, hg, n, hn, rfl⟩ := (hu a).mp ((hr a b).mp hab).1
    obtain ⟨g', hg', n', hn', rfl⟩ := (hu b).mp ((hr _ b).mp hab).2.1
    obtain ⟨g'', hg'', n'', hn'', rfl⟩ := (hu c).mp ((hr _ c).mp hbc).2.1
    refine (hrk g n g'' n'').mpr ⟨hg, hn, hg'', hn'', ?_⟩
    rcases ((hrk g n g' n').mp hab).2.2.2.2 with h1 | ⟨rfl, h1⟩
    · rcases ((hrk g' n' g'' n'').mp hbc).2.2.2.2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl ((ord_mem hS hg'').1 g' h2 g h1)
      · exact Or.inl h1
    · rcases ((hrk g n' g'' n'').mp hbc).2.2.2.2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, (ord_mem ord_om hn'').1 n' h2 n h1⟩
  -- the values are ordinals
  have hOrd : ∀ a, a ∈ u → ∀ v, Pr F a v → Ord v := by
    by_contra hcon
    let Z : V := sepB (k := 1) (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and
      (ordB.comp ![0]).not)))) u ![F]
    have hZ : ∀ a, a ∈ Z ↔ a ∈ u ∧ ∃ q, q ∈ F ∧ ∃ w, w ∈ q ∧ ∃ y, y ∈ w ∧
        (IsOp q a y ∧ ¬Ord y) := fun a => mem_sepB _ _ _ a
    have hne : ∃ a, a ∈ Z ∧ ¬False := by
      by_contra h
      refine hcon fun a ha v hv => ?_
      by_contra hn
      obtain ⟨q, hq, hop⟩ := hv
      obtain ⟨w, hw, hyw⟩ := pr_snd_mem hop
      exact h ⟨a, (hZ a).mpr ⟨ha, q, hq, w, hw, v, hyw, hop, hn⟩, id⟩
    obtain ⟨a, haZ, hmin⟩ := hwf Z hne (fun c hc => ((hZ c).mp hc).1)
    obtain ⟨hau, q, hq, w, -, y, -, hop, hny⟩ := (hZ a).mp haZ
    obtain ⟨v, -, hav, hvu, hvm⟩ := hFv a hau
    have e : y = v := hvu y ⟨q, hq, hop⟩
    subst e
    have hsmall : ∀ a', a' ∈ u → Pr r a' a → ∀ y', Pr F a' y' → Ord y' := by
      intro a' ha' hra y' hy'
      by_contra hn
      obtain ⟨q', hq', hop'⟩ := hy'
      obtain ⟨w', hw', hyw'⟩ := pr_snd_mem hop'
      exact hmin a' ((hZ a').mpr ⟨ha', q', hq', w', hw', y', hyw', hop', hn⟩) hra
    refine hny ⟨fun z hz t ht => ?_, fun z hz => ?_⟩
    · obtain ⟨a', ha', hra, hFa'⟩ := (hvm z).mp hz
      obtain ⟨v', -, hav', hvu', hvm'⟩ := hFv a' ha'
      have e : z = v' := hvu' z hFa'
      subst e
      obtain ⟨a'', ha'', hra', hFa''⟩ := (hvm' t).mp ht
      exact (hvm t).mpr ⟨a'', ha'', hrtrans _ _ _ hra' hra, hFa''⟩
    · obtain ⟨a', ha', hra, hFa'⟩ := (hvm z).mp hz
      exact (hsmall a' ha' hra z hFa').1
  let lam : V := sepB (k := 2) (BDef.bex 1 (prB.comp ![3, 0, 1])) T ![u, F]
  have hlam : ∀ y, y ∈ lam ↔ y ∈ T ∧ ∃ a, a ∈ u ∧ Pr F a y := fun y => mem_sepB _ _ _ y
  have hlamO : Ord lam := by
    refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
    · obtain ⟨-, a, ha, hay⟩ := (hlam y).mp hy
      obtain ⟨v, -, hav, hvu, hvm⟩ := hFv a ha
      have e : y = v := hvu y hay
      subst e
      obtain ⟨a', ha', -, hFa'⟩ := (hvm z).mp hz
      obtain ⟨v', hv'T, -, hvu', -⟩ := hFv a' ha'
      exact (hlam z).mpr ⟨hvu' z hFa' ▸ hv'T, a', ha', hFa'⟩
    · obtain ⟨-, a, ha, hay⟩ := (hlam y).mp hy
      exact (hOrd a ha y hay).1
  -- the value at the successor of `⟨γ, n⟩`
  have hsucc : ∀ γ, γ ∈ S → ∀ n, n ∈ (om : V) → ∀ v v', Pr F (kp γ n) v →
      Pr F (kp γ (sc n)) v' → v' = sc v := by
    intro γ hγ n hn v v' hv hv'
    have hau : kp γ n ∈ u := (hu _).mpr ⟨γ, hγ, n, hn, rfl⟩
    have hau' : kp γ (sc n) ∈ u := (hu _).mpr ⟨γ, hγ, sc n, sc_mem_om hn, rfl⟩
    obtain ⟨w, -, haw, hwu, hwm⟩ := hFv _ hau
    obtain ⟨w', -, haw', hwu', hwm'⟩ := hFv _ hau'
    have e : v = w := hwu v hv
    have e' : v' = w' := hwu' v' hv'
    subst e e'
    refine mem_ext fun y => ?_
    rw [hwm', mem_sc, hwm]
    constructor
    · rintro ⟨a', ha', hra, hFa'⟩
      obtain ⟨g, hg, m, hm, rfl⟩ := (hu a').mp ha'
      rcases ((hrk g m γ (sc n)).mp hra).2.2.2.2 with h | ⟨rfl, h⟩
      · exact Or.inr ⟨_, ha', (hrk g m γ n).mpr ⟨hg, hm, hγ, hn, Or.inl h⟩, hFa'⟩
      · rcases mem_sc.mp h with rfl | h
        · exact Or.inl (hwu y hFa')
        · exact Or.inr ⟨_, ha', (hrk g m g n).mpr ⟨hg, hm, hγ, hn, Or.inr ⟨rfl, h⟩⟩, hFa'⟩
    · rintro (rfl | ⟨a', ha', hra, hFa'⟩)
      · exact ⟨_, hau, (hrk γ n γ (sc n)).mpr ⟨hγ, hn, hγ, sc_mem_om hn,
          Or.inr ⟨rfl, self_mem_sc n⟩⟩, hv⟩
      · obtain ⟨g, hg, m, hm, rfl⟩ := (hu a').mp ha'
        refine ⟨_, ha', (hrk g m γ (sc n)).mpr ⟨hg, hm, hγ, sc_mem_om hn, ?_⟩, hFa'⟩
        rcases ((hrk g m γ n).mp hra).2.2.2.2 with h | ⟨rfl, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl, mem_sc.mpr (Or.inr h)⟩
  have hval : ∀ a, a ∈ u → ∃ v, Pr F a v ∧ v ∈ lam := fun a ha => by
    obtain ⟨v, hvT, hav, -, -⟩ := hFv a ha
    exact ⟨v, hav, (hlam v).mpr ⟨hvT, a, ha, hav⟩⟩
  have hlim : Lim lam := by
    refine ⟨hlamO, ?_, fun y hy => ?_⟩
    · obtain ⟨v, -, hv⟩ := hval (kp γ₀ ∅) ((hu _).mpr ⟨γ₀, self_mem_sc γ₀, ∅, empty_mem_om, rfl⟩)
      exact ⟨v, hv⟩
    · obtain ⟨-, a, ha, hay⟩ := (hlam y).mp hy
      obtain ⟨g, hg, n, hn, rfl⟩ := (hu a).mp ha
      obtain ⟨v', hv', hv'lam⟩ := hval (kp g (sc n)) ((hu _).mpr ⟨g, hg, sc n, sc_mem_om hn, rfl⟩)
      rw [← hsucc g hg n hn y v' hay hv']
      exact hv'lam
  refine ⟨lam, hlim, ?_⟩
  -- `γ ⊆ F ⟨γ, 0⟩` for `γ ≤ γ₀`
  have hsub : ∀ γ, γ ∈ S → ∀ v, Pr F (kp γ ∅) v → ∀ z, z ∈ γ → z ∈ v := by
    by_contra hcon
    let Z : V := sepB (k := 4) (BDef.bex 1 ((isOpB.comp ![0, 1, 4]).and (BDef.bex 5
      ((prB.comp ![4, 1, 0]).and (BDef.bex 2 (BDef.mem 0 1).not))))) S ![u, F, (∅ : V), T]
    have hZ : ∀ γ, γ ∈ Z ↔ γ ∈ S ∧ ∃ a, a ∈ u ∧ (IsOp a γ (∅ : V) ∧ ∃ v, v ∈ T ∧
        (Pr F a v ∧ ∃ z, z ∈ γ ∧ ¬z ∈ v)) := fun γ => mem_sepB _ _ _ γ
    have hne : ∃ γ, γ ∈ Z := by
      by_contra h
      refine hcon fun γ hγ v hv z hz => ?_
      by_contra hn
      have hau : kp γ (∅ : V) ∈ u := (hu _).mpr ⟨γ, hγ, ∅, empty_mem_om, rfl⟩
      obtain ⟨v', hv'T, -, hvu', -⟩ := hFv _ hau
      exact h ⟨γ, (hZ γ).mpr ⟨hγ, _, hau, isOp_kp γ ∅, v, hvu' v hv ▸ hv'T, hv, z, hz, hn⟩⟩
    obtain ⟨γ, hγZ, hmin⟩ := ord_least Z (fun z hz => ord_mem hS ((hZ z).mp hz).1) hne
    obtain ⟨hγS, a, hau, hop, v, -, hav, z, hzγ, hzv⟩ := (hZ γ).mp hγZ
    have ea : a = kp γ ∅ := isOp_iff.mp hop
    subst ea
    have hzS : z ∈ S := hS.1 γ hγS z hzγ
    have hzu : kp z (∅ : V) ∈ u := (hu _).mpr ⟨z, hzS, ∅, empty_mem_om, rfl⟩
    obtain ⟨vz, hvzT, hvz, -, -⟩ := hFv _ hzu
    have hzsub : ∀ t, t ∈ z → t ∈ vz := by
      intro t ht
      by_contra hn
      rcases hmin z ((hZ z).mpr ⟨hzS, _, hzu, isOp_kp z ∅, vz, hvzT, hvz, t, ht, hn⟩) with e | e
      · exact mem_irrefl γ (e ▸ hzγ)
      · exact mem_asymm e hzγ
    obtain ⟨w, -, haw, hwu, hwm⟩ := hFv _ hau
    have e : v = w := hwu v hav
    subst e
    have hvzv : vz ∈ v := (hwm vz).mpr ⟨_, hzu, (hrk z ∅ γ ∅).mpr
      ⟨hzS, empty_mem_om, hγS, empty_mem_om, Or.inl hzγ⟩, hvz⟩
    have hvO : Ord v := hOrd _ hau v hav
    rcases (ord_le_iff (ord_mem hS hzS) (hOrd _ hzu vz hvz)).mp hzsub with e | e
    · exact hzv (e ▸ hvzv)
    · exact hzv (hvO.1 vz hvzv z e)
  obtain ⟨v, hv, hvlam⟩ := hval (kp γ₀ ∅) ((hu _).mpr ⟨γ₀, self_mem_sc γ₀, ∅, empty_mem_om, rfl⟩)
  have hvO : Ord v := hOrd _ ((hu _).mpr ⟨γ₀, self_mem_sc γ₀, ∅, empty_mem_om, rfl⟩) v hv
  rcases (ord_le_iff h₀ hvO).mp (hsub γ₀ (self_mem_sc γ₀) v hv) with e | e
  · exact e ▸ hvlam
  · exact hlamO.1 v hvlam γ₀ e

end lim

end MH

end FFL.FirstOrder.SetTheory
