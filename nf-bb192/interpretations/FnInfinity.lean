import FnSets

set_option autoImplicit false

/-!
# Inside a model of FunctionNF: the universe is not finite

Fix a model `M` of `𝗙𝗡𝗙`, with the membership relation `Mem` of `FnBool.lean`. This file proves
`univInfinite : UnivInfinite Mem`, the form of the axiom of infinity used for `𝗡𝗙𝗨𝗜`.

The proof is by contradiction and follows Specker's refutation of the axiom of choice in NF,
with one change: where NF has `P(V) ⊆ V`, here every object is a function and a function is
determined by its graph, so the set of double singletons of all objects injects into
`P(P(P(V)))` (`lemB`). Sets of all objects inject back because sets are objects (`lemA`).

* `Ex b a`: `b` is equinumerous with a set of singletons `simg y`, and `a` with `pow y`
  ("`a` is two to the power `b`").
* `Tw i a`, for `i : Fin 5`: `a` is in the tower `2, 2², 2^2², …`, at a position congruent to
  `i` modulo 5. It is the least family of five sets closed under the two rules.
* `tw_ind`: induction on the tower. `tw_inv`, `tw_simg`, `tw_D` (two tower terms are
  comparable, and nothing lies strictly between a term and the next), `tw_res` (the position
  modulo 5 is determined by the size).
* `fin_ind`: if the universe is finite, a property with a truth-value term that holds of the
  objects without members and is preserved by adjoining one element holds of every object.
  `comparable`, `exists_top` (the tower has a last term below a set of singletons).
* `univInfinite`: the last tower term `τ` below `w = simg (simg univ)` satisfies
  `pow τ ≼ τ` and `τ ≼ pow (pow (pow (pow τ)))` after three applications of `simg`, which puts
  its position modulo 5 among the next four positions.
-/

namespace FFL.FirstOrder.FNF

open JensenNFU (UnivInfinite)
open JensenNFU.TFm (scons scons_zero scons_succ)

variable {M : Type} [s : Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

local infixl:70 " ⬝ " => App

/-- Keep the first variable and skip the second. -/
def skp : ℕ → ℕ
  | 0 => 0
  | i + 1 => i + 2

noncomputable section

/-! ### Sets with two or three elements -/

/-- `a` has exactly two members. -/
def Two (a : M) : Prop := ∃ x y, x ≠ y ∧ ∀ z, Mem z a ↔ z = x ∨ z = y

/-- `a` has at least two members. -/
def Ge2 (a : M) : Prop := ∃ x y, Mem x a ∧ Mem y a ∧ x ≠ y

/-- `a` has at least three members. -/
def Three (a : M) : Prop :=
  ∃ x y z, Mem x a ∧ Mem y a ∧ Mem z a ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z

def twoB : BT [1] (fun v : ℕ → M => Two (v 0)) :=
  BT.congr (BT.ex 0 (BT.ex 0 (((BT.eq 1 0 0 rfl rfl).not).and
    (BT.all 0 ((BT.mem 0 3 0 rfl rfl).iff ((BT.eq 0 2 0 rfl rfl).or (BT.eq 0 1 0 rfl rfl)))))))
    fun _ => Iff.rfl

def ge2B : BT [1] (fun v : ℕ → M => Ge2 (v 0)) :=
  BT.congr (BT.ex 0 (BT.ex 0 ((BT.mem 1 2 0 rfl rfl).and
    ((BT.mem 0 2 0 rfl rfl).and ((BT.eq 1 0 0 rfl rfl).not)))))
    fun _ => Iff.rfl

theorem two_ge2 {a : M} (h : Two a) : Ge2 a := by
  obtain ⟨x, y, hne, hm⟩ := h
  exact ⟨x, y, (hm x).mpr (Or.inl rfl), (hm y).mpr (Or.inr rfl), hne⟩

theorem two_upr {x y : M} (h : x ≠ y) : Two (upr x y) := ⟨x, y, h, fun _ => mem_upr⟩

theorem two_le {a b : M} (ha : Two a) (hb : Ge2 b) : Le a b := by
  obtain ⟨x₁, x₂, hne, hm⟩ := ha
  obtain ⟨y₁, y₂, h1, h2, hne'⟩ := hb
  refine le_of_rel (t := 0) (Γ := [0, 0, 0, 0])
    (((BT.eq 0 2 0 rfl rfl).and (BT.eq 1 3 0 rfl rfl)).or
      ((BT.eq 0 4 0 rfl rfl).and (BT.eq 1 5 0 rfl rfl)))
    (scons x₁ (scons y₁ (scons x₂ (fun _ => y₂))))
    (fun x y => (x = x₁ ∧ y = y₁) ∨ (x = x₂ ∧ y = y₂)) (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
  · rintro x y (⟨e1, e2⟩ | ⟨e1, e2⟩)
    · rw [e1, e2]; exact ⟨(hm _).mpr (Or.inl rfl), h1⟩
    · rw [e1, e2]; exact ⟨(hm _).mpr (Or.inr rfl), h2⟩
  · intro x hx
    rcases (hm x).mp hx with e | e
    · exact ⟨y₁, Or.inl ⟨e, rfl⟩⟩
    · exact ⟨y₂, Or.inr ⟨e, rfl⟩⟩
  · rintro x y y' (⟨e1, e2⟩ | ⟨e1, e2⟩) (⟨e1', e2'⟩ | ⟨e1', e2'⟩)
    · rw [e2, e2']
    · exact absurd (e1.symm.trans e1') hne
    · exact absurd (e1'.symm.trans e1) hne
    · rw [e2, e2']
  · rintro x x' y (⟨e1, e2⟩ | ⟨e1, e2⟩) (⟨e1', e2'⟩ | ⟨e1', e2'⟩)
    · rw [e1, e1']
    · exact absurd (e2.symm.trans e2') hne'
    · exact absurd (e2'.symm.trans e2) hne'
    · rw [e1, e1']

theorem ge2_of_le {a b : M} (ha : Ge2 a) (h : Le a b) : Ge2 b := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨x, y, hx, hy, hne⟩ := ha
  obtain ⟨x', hx'⟩ := hf.tot x hx
  obtain ⟨y', hy'⟩ := hf.tot y hy
  refine ⟨x', y', (hf.dom _ _ hx').2, (hf.dom _ _ hy').2, fun e => hne ?_⟩
  rw [e] at hx'
  exact hf.inj _ _ _ hx' hy'

theorem three_of_le {a b : M} (ha : Three a) (h : Le a b) : Three b := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨p, q, r, hp, hq, hr, h1, h2, h3⟩ := ha
  obtain ⟨p', hp'⟩ := hf.tot p hp
  obtain ⟨q', hq'⟩ := hf.tot q hq
  obtain ⟨r', hr'⟩ := hf.tot r hr
  refine ⟨p', q', r', (hf.dom _ _ hp').2, (hf.dom _ _ hq').2, (hf.dom _ _ hr').2,
    fun e => h1 ?_, fun e => h2 ?_, fun e => h3 ?_⟩
  · rw [e] at hp'; exact hf.inj _ _ _ hp' hq'
  · rw [e] at hp'; exact hf.inj _ _ _ hp' hr'
  · rw [e] at hq'; exact hf.inj _ _ _ hq' hr'

theorem not_three_of_two {a : M} (h : Two a) : ¬Three a := by
  rintro ⟨p, q, r, hp, hq, hr, h1, h2, h3⟩
  obtain ⟨x, y, -, hm⟩ := h
  rcases (hm p).mp hp with e1 | e1 <;> rcases (hm q).mp hq with e2 | e2 <;>
    rcases (hm r).mp hr with e3 | e3
  · exact h1 (e1.trans e2.symm)
  · exact h1 (e1.trans e2.symm)
  · exact h2 (e1.trans e3.symm)
  · exact h3 (e2.trans e3.symm)
  · exact h3 (e2.trans e3.symm)
  · exact h2 (e1.trans e3.symm)
  · exact h1 (e1.trans e2.symm)
  · exact h1 (e1.trans e2.symm)

theorem ge2_simg {y : M} (h : Ge2 (simg y)) : Ge2 y := by
  obtain ⟨u, t, hu, ht, hne⟩ := h
  obtain ⟨x, hx, rfl⟩ := mem_simg.mp hu
  obtain ⟨x', hx', rfl⟩ := mem_simg.mp ht
  exact ⟨x, x', hx, hx', fun e => hne (by rw [e])⟩

theorem two_simg {a : M} (h : Two a) : Two (simg a) := by
  obtain ⟨x, y, hne, hm⟩ := h
  refine ⟨sing x, sing y, fun e => hne (sing_inj e), fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨u, hu, rfl⟩ := mem_simg.mp hz
    rcases (hm u).mp hu with e | e
    · exact Or.inl (by rw [e])
    · exact Or.inr (by rw [e])
  · rcases hz with e | e
    · rw [e]; exact mem_simg_sing.mpr ((hm x).mpr (Or.inl rfl))
    · rw [e]; exact mem_simg_sing.mpr ((hm y).mpr (Or.inr rfl))

theorem ge2_pow {y x : M} (hx : Mem x y) : Ge2 (pow y) :=
  ⟨emp, y, mem_pow.mpr ⟨isSet_emp, fun z hz => absurd hz (not_mem_emp z)⟩,
    mem_pow.mpr ⟨hx.1, fun _ h => h⟩, fun e => not_mem_emp x (by rw [e]; exact hx)⟩

theorem three_pow {y : M} (hy : Ge2 y) : Three (pow y) := by
  obtain ⟨u₁, u₂, h1, h2, hne⟩ := hy
  have hs : ∀ u, Mem u y → Mem (sing u) (pow y) := fun u hu =>
    mem_pow.mpr ⟨isSet_sing, fun z hz => by rw [mem_sing.mp hz]; exact hu⟩
  have he : ∀ u : M, emp ≠ sing u := fun u e =>
    not_mem_emp u (by rw [e]; exact mem_sing.mpr rfl)
  exact ⟨emp, sing u₁, sing u₂, mem_pow.mpr ⟨isSet_emp, fun z hz => absurd hz (not_mem_emp z)⟩,
    hs u₁ h1, hs u₂ h2, he u₁, he u₂, fun e => hne (sing_inj e)⟩

theorem two_eqv_simg {a : M} (ha : Two a) : ∃ y : M, Two y ∧ Eqv a (simg y) :=
  ⟨upr TT FF, two_upr (tt_ne_ff hM),
    two_le ha (two_ge2 (two_simg (two_upr (tt_ne_ff hM)))),
    two_le (two_simg (two_upr (tt_ne_ff hM))) (two_ge2 ha)⟩

/-! ### Exponentiation -/

/-- `b` is equinumerous with a set of singletons `simg y` and `a` with `pow y`. -/
def Ex (b a : M) : Prop := ∃ y, Eqv b (simg y) ∧ Eqv a (pow y)

def exB : BT [2, 2] (fun v : ℕ → M => Ex (v 0) (v 1)) :=
  BT.congr (BT.ex 1 (BT.ex 2 ((simgB.sub [0, 1] 0).and ((eqvB.sub [2, 0] 1).and
    (BT.ex 2 ((powB.sub [0, 2] 0).and (eqvB.sub [4, 0] 1)))))))
    fun v => ⟨fun ⟨y, u, (h1 : u = simg y), (h2 : Eqv (v 0) u), t, (h3 : t = pow y),
      (h4 : Eqv (v 1) t)⟩ => by subst h1 h3; exact ⟨y, h2, h4⟩,
      fun ⟨y, h1, h2⟩ => ⟨y, _, rfl, h1, _, rfl, h2⟩⟩

theorem ex_self (y : M) : Ex (simg y) (pow y) := ⟨y, eqv_refl _, eqv_refl _⟩

theorem ex_mono {b a b' a' : M} (h1 : Ex b a) (h2 : Ex b' a') (h : Le b b') : Le a a' := by
  obtain ⟨y, hb, ha⟩ := h1
  obtain ⟨y', hb', ha'⟩ := h2
  have : Le y y' := le_of_simg (le_trans hb.2 (le_trans h hb'.1))
  exact le_trans ha.1 (le_trans (le_pow this) ha'.2)

theorem ex_simg {b a : M} (h : Ex b a) : Ex (simg b) (simg a) := by
  obtain ⟨y, hb, ha⟩ := h
  exact ⟨simg y, ⟨le_simg hb.1, le_simg hb.2⟩,
    ⟨le_trans (le_simg ha.1) (simg_pow_le y), le_trans (pow_simg_le y) (le_simg ha.2)⟩⟩

theorem ex_of_le_simg {b z : M} (h : Le b (simg z)) : ∃ e, Ex b e := by
  obtain ⟨y, hy⟩ := le_simg_ex h
  exact ⟨pow y, y, hy, eqv_refl _⟩

/-! ### The tower -/

/-- The five sets `X` contain the sets with two elements and are closed under exponentiation,
which moves from one set to the next. -/
def Ind (X : Fin 5 → M) : Prop :=
  (∀ a, Two a → Mem a (X 0)) ∧ ∀ i : Fin 5, ∀ b a, Mem b (X i) → Ex b a → Mem a (X (i + 1))

/-- `a` is in the tower, at a position congruent to `i` modulo 5. -/
def Tw (i : Fin 5) (a : M) : Prop := ∀ X : Fin 5 → M, Ind X → Mem a (X i)

def indB {Γ : List ℕ} :
    BT (3 :: 3 :: 3 :: 3 :: 3 :: Γ) (fun v : ℕ → M => Ind (fun j : Fin 5 => v j)) :=
  BT.congr ((BT.all 2 ((twoB.sub [0] 1).imp (BT.mem 0 1 2 rfl rfl))).and
    (BT.forallFin (fun i : Fin 5 => BT.all 2 (BT.all 2
      ((BT.mem 1 ((i : ℕ) + 2) 2 rfl (by fin_cases i <;> rfl)).imp
        ((exB.sub [1, 0] 0).imp
          (BT.mem 0 (((i + 1 : Fin 5) : ℕ) + 2) 2 rfl (by fin_cases i <;> rfl))))))))
    fun _ => Iff.rfl

def twB {Γ : List ℕ} (i : Fin 5) : BT (2 :: Γ) (fun v : ℕ → M => Tw i (v 0)) :=
  BT.congr (BT.all 3 (BT.all 3 (BT.all 3 (BT.all 3 (BT.all 3
    (indB.imp (BT.mem 5 (i : ℕ) 2 rfl (by fin_cases i <;> rfl))))))))
    fun v => ⟨fun h X hX => by
        have e : (fun j : Fin 5 => scons (X 0) (scons (X 1) (scons (X 2) (scons (X 3)
            (scons (X 4) v)))) (j : ℕ)) = X := by
          funext j; fin_cases j <;> rfl
        have hX' : Ind (fun j : Fin 5 => scons (X 0) (scons (X 1) (scons (X 2) (scons (X 3)
            (scons (X 4) v)))) (j : ℕ)) := by rw [e]; exact hX
        exact Eq.mp (congrArg (Mem (v 0)) (congrFun e i)) (h (X 4) (X 3) (X 2) (X 1) (X 0) hX'),
      fun h _ _ _ _ _ hI => h _ hI⟩

theorem tw_base {a : M} (h : Two a) : Tw 0 a := fun _ hX => hX.1 a h

theorem tw_step {i : Fin 5} {b a : M} (h : Tw i b) (he : Ex b a) : Tw (i + 1) a :=
  fun X hX => hX.2 i b a (h X hX) he

/-- **Induction on the tower.** -/
theorem tw_ind {Γ : List ℕ} {Φ : Fin 5 → (ℕ → M) → Prop} (p : ∀ i, BT (2 :: Γ) (Φ i))
    (q : ℕ → M) (h0 : ∀ a, Two a → Φ 0 (scons a q))
    (hs : ∀ i b a, Tw i b → Φ i (scons b q) → Ex b a → Φ (i + 1) (scons a q)) :
    ∀ i a, Tw i a → Φ i (scons a q) := by
  have hY : ∀ i : Fin 5, ∃ y : M, IsSet y ∧ ∀ x, Mem x y ↔ Tw i x ∧ Φ i (scons x q) :=
    fun i => ((twB i).and (p i)).set q
  choose Y _ hY using hY
  have hI : Ind Y := ⟨fun a ha => (hY 0 a).mpr ⟨tw_base ha, h0 a ha⟩, fun i b a hb he => by
    obtain ⟨hb1, hb2⟩ := (hY i b).mp hb
    exact (hY (i + 1) a).mpr ⟨tw_step hb1 he, hs i b a hb1 hb2 he⟩⟩
  intro i a ha
  exact ((hY i a).mp (ha Y hI)).2

/-- A tower term has at least two members. -/
theorem tw_ge2 {i : Fin 5} {a : M} (h : Tw i a) : Ge2 a := by
  refine tw_ind (Γ := []) (Φ := fun _ v => Ge2 (v 0)) (fun _ => ge2B.sub [0] 1) (fun _ => a)
    (fun a ha => two_ge2 ha) ?_ i a h
  intro i b a _ hb he
  obtain ⟨y, hby, hay⟩ := he
  obtain ⟨x, _, hx, _, _⟩ := ge2_simg (ge2_of_le hb hby.1)
  exact ge2_of_le (ge2_pow hx) hay.2

theorem tw_three {i : Fin 5} {b a : M} (hb : Tw i b) (he : Ex b a) : Three a := by
  obtain ⟨y, hby, hay⟩ := he
  exact three_of_le (three_pow (ge2_simg (ge2_of_le (tw_ge2 hb) hby.1))) hay.2

/-- A tower term has two elements, or is obtained from a tower term by exponentiation. -/
theorem tw_inv {i : Fin 5} {a : M} (h : Tw i a) :
    (i = 0 ∧ Two a) ∨ ∃ b, Tw (i - 1) b ∧ Ex b a := by
  refine tw_ind (Γ := [])
    (Φ := fun i v => (i = 0 ∧ Two (v 0)) ∨ ∃ b, Tw (i - 1) b ∧ Ex b (v 0))
    (fun i => ((BT.const (i = 0)).and (twoB.sub [0] 1)).or
      (BT.ex 2 ((twB (i - 1)).and (exB.sub [0, 1] 0))))
    (fun _ => a) (fun a ha => Or.inl ⟨rfl, ha⟩) ?_ i a h
  intro i b a hb _ he
  exact Or.inr ⟨b, by simpa using hb, he⟩

/-- The set of singletons of the members of a tower term is a tower term at the same
position. -/
theorem tw_simg {i : Fin 5} {a : M} (h : Tw i a) : Tw i (simg a) := by
  have := tw_ind (Γ := []) (Φ := fun i v => ∃ u, u = simg (v 0) ∧ Tw i u)
    (fun i => BT.ex 3 ((simgB.sub [0, 1] 1).and ((twB (Γ := []) i).sub [0] 1)))
    (fun _ => a) (fun a ha => ⟨_, rfl, tw_base (two_simg ha)⟩)
    (fun i b a _ ⟨u, (hu : u = simg b), (hb : Tw i u)⟩ he =>
      ⟨_, rfl, tw_step (by subst hu; exact hb) (ex_simg he)⟩) i a h
  obtain ⟨u, (hu : u = simg a), hu'⟩ := this
  subst hu
  exact hu'

/-- Two tower terms: the second injects into the first, or the exponential of the first injects
into the second. -/
theorem tw_D {i j : Fin 5} {κ μ : M} (hκ : Tw i κ) (hμ : Tw j μ) :
    Le μ κ ∨ ∃ e, Ex κ e ∧ Le e μ := by
  have := tw_ind (Γ := [])
    (Φ := fun _ v => ∀ j : Fin 5, ∀ m, Tw j m → Le m (v 0) ∨ ∃ e, Ex (v 0) e ∧ Le e m)
    (fun _ => BT.forallFin (fun j => BT.all 2 ((twB j).imp ((leB.sub [0, 1] 1).or
      (BT.ex 2 ((exB.sub [2, 0] 0).and (leB.sub [0, 1] 1)))))))
    (fun _ => κ) ?base ?step i κ hκ
  · exact this j μ hμ
  case base =>
    intro a ha j m hm
    rcases tw_inv hm with ⟨-, hm2⟩ | ⟨b, hb, hbm⟩
    · exact Or.inl (two_le hm2 (two_ge2 ha))
    · right
      obtain ⟨y, hy2, hy⟩ := two_eqv_simg ha
      refine ⟨pow y, ⟨y, hy, eqv_refl _⟩, ?_⟩
      obtain ⟨y', hby', hmy'⟩ := hbm
      have hy' : Ge2 y' := ge2_simg (ge2_of_le (tw_ge2 hb) hby'.1)
      exact le_trans (le_pow (two_le hy2 hy')) hmy'.2
  case step =>
    intro i κ κ' hκ ih he j m hm
    rcases tw_inv hm with ⟨-, hm2⟩ | ⟨b, hb, hbm⟩
    · exact Or.inl (two_le hm2 (tw_ge2 (tw_step hκ he)))
    · rcases ih (j - 1) b hb with h | ⟨e, hκe, heb⟩
      · exact Or.inl (ex_mono hbm he h)
      · right
        have hκ'b : Le κ' b := le_trans (ex_mono he hκe (le_refl _)) heb
        obtain ⟨y', hby', hmy'⟩ := hbm
        obtain ⟨e', he'⟩ := ex_of_le_simg (le_trans hκ'b hby'.1)
        exact ⟨e', he', ex_mono he' ⟨y', hby', hmy'⟩ hκ'b⟩

/-- Equinumerous tower terms are at the same position modulo 5. -/
theorem tw_res {i j : Fin 5} {a a' : M} (ha : Tw i a) (ha' : Tw j a') (h : Eqv a a') :
    j = i := by
  have := tw_ind (Γ := [])
    (Φ := fun i v => ∀ j : Fin 5, ∀ m, Tw j m → Eqv (v 0) m → j = i)
    (fun i => BT.forallFin (fun j => BT.all 2 ((twB j).imp
      ((eqvB.sub [1, 0] 1).imp (BT.const (j = i))))))
    (fun _ => a) ?base ?step i a ha
  · exact this j a' ha' h
  case base =>
    intro a ha j m hm hEq
    rcases tw_inv hm with ⟨hj, -⟩ | ⟨b, hb, hbm⟩
    · exact hj
    · exact absurd (three_of_le (tw_three hb hbm) hEq.2) (not_three_of_two ha)
  case step =>
    intro i b a hb ih he j m hm hEq
    rcases tw_inv hm with ⟨-, hm2⟩ | ⟨b', hb', hb'm⟩
    · exact absurd (three_of_le (tw_three hb he) hEq.1) (not_three_of_two hm2)
    · have h1 : Le b' b := by
        rcases tw_D hb hb' with h | ⟨e, hbe, heb'⟩
        · exact h
        · exfalso
          have : Le m b' := le_trans hEq.2 (le_trans (ex_mono he hbe (le_refl _)) heb')
          obtain ⟨y', hy1, hy2⟩ := hb'm
          exact cantor y' (le_trans hy2.2 (le_trans this hy1.1))
      have h2 : Le b b' := by
        rcases tw_D hb' hb with h | ⟨e, hb'e, heb⟩
        · exact h
        · exfalso
          have : Le a b := le_trans hEq.1 (le_trans (ex_mono hb'm hb'e (le_refl _)) heb)
          obtain ⟨y, hy1, hy2⟩ := he
          exact cantor y (le_trans hy2.2 (le_trans this hy1.1))
      have := ih (j - 1) b' hb' ⟨h2, h1⟩
      rw [← this]
      simp

/-! ### Finite induction -/

/-- **Finite induction.** If the universe is finite, a property with a truth-value term that
holds of the objects without members and is preserved by adjoining one element holds of every
object. -/
theorem fin_ind (hfin : ¬UnivInfinite (Mem (M := M))) {t : ℕ} {Γ : List ℕ}
    {R : (ℕ → M) → Prop} (p : BT ((t + 1) :: Γ) R) (q : ℕ → M)
    (h0 : ∀ e, (∀ z, ¬Mem z e) → R (scons e q))
    (hs : ∀ a b a', R (scons a q) → (∀ z, Mem z a' ↔ Mem z a ∨ z = b) → R (scons a' q)) :
    ∀ a, R (scons a q) := by
  obtain ⟨F, -, hF⟩ := (BT.all (Γ := (t + 1) :: Γ) (t + 1)
    ((subB.comp (nth [0, 1]) t (fun i hi => by
      match i, hi with
      | 0, _ => show some (t + 1) = some (1 + t); rw [Nat.add_comm]
      | 1, _ => show some (t + 1) = some (1 + t); rw [Nat.add_comm]
      | i + 2, hi => exact absurd hi (by simp))).imp
    (p.comp skp 0 (fun i hi => by
      match i, hi with
      | 0, _ => rfl
      | i + 1, hi =>
        have hi' : i < Γ.length := by simpa using hi
        show Γ[i]? = some (Γ[i] + 0)
        rw [List.getElem?_eq_getElem hi']; rfl)))).set q
  have e : ∀ u a : M, (fun i => scons u (scons a q) (skp i)) = scons u q := by
    intro u a
    funext i
    match i with
    | 0 => rfl
    | i + 1 => rfl
  have hF' : ∀ a, Mem a F ↔ ∀ u, Sub u a → R (scons u q) := by
    intro a
    refine (hF a).trans (forall_congr' fun u => imp_congr Iff.rfl ?_)
    show R (fun i => scons u (scons a q) (skp i)) ↔ _
    rw [e]
  have hbase : ∀ e, (∀ z, ¬Mem z e) → Mem e F := fun e he =>
    (hF' e).mpr fun u hu => h0 u fun z hz => he z (hu z hz)
  have hstep : ∀ a, Mem a F → ∀ b a', (∀ z, Mem z a' ↔ Mem z a ∨ z = b) → Mem a' F := by
    intro a ha b a' ha'
    refine (hF' a').mpr fun u hu => ?_
    obtain ⟨u₀, hu₀, hm⟩ := ((BT.mem (Γ := [0, 1, 0]) 0 1 0 rfl rfl).and
      ((BT.eq 0 2 0 rfl rfl).not)).set (scons u (fun _ => b))
    have hm' : ∀ z, Mem z u₀ ↔ Mem z u ∧ ¬z = b := hm
    have h1 : R (scons u₀ q) := (hF' a).mp ha u₀ fun z hz => by
      obtain ⟨hz1, hz2⟩ := (hm' z).mp hz
      exact ((ha' z).mp (hu z hz1)).resolve_right hz2
    by_cases hb : Mem b u
    · refine hs u₀ b u h1 fun z => ⟨fun hz => ?_, fun hz => ?_⟩
      · by_cases e : z = b
        · exact Or.inr e
        · exact Or.inl ((hm' z).mpr ⟨hz, e⟩)
      · rcases hz with hz | e
        · exact ((hm' z).mp hz).1
        · rw [e]; exact hb
    · by_cases hne : ∃ z, Mem z u
      · obtain ⟨z₀, hz₀⟩ := hne
        have : u = u₀ := set_ext hz₀.1 hu₀ fun z =>
          ⟨fun hz => (hm' z).mpr ⟨hz, fun e => hb (by rw [← e]; exact hz)⟩,
            fun hz => ((hm' z).mp hz).1⟩
        rw [this]; exact h1
      · exact h0 u fun z hz => hne ⟨z, hz⟩
  obtain ⟨u, hu, huF⟩ : ∃ u, (∀ z, Mem z u) ∧ Mem u F := by
    by_contra hne
    exact hfin ⟨F, hbase, hstep, fun u hu huF => hne ⟨u, hu, huF⟩⟩
  intro a
  exact (hF' u).mp huF a fun z _ => hu z

/-- Extend an injection that is not onto by one pair. -/
theorem le_adjoin {f a b c d a' : M} (hf : Inj f a b) (hc : ¬Mem c a) (hd : Mem d b)
    (hd' : ∀ x, ¬Ap f x d) (ha' : ∀ z, Mem z a' ↔ Mem z a ∨ z = c) : Le a' b := by
  refine le_of_rel (t := 0) (Γ := [3, 0, 0])
    ((apB.sub [2, 0, 1] 0).or ((BT.eq 0 3 0 rfl rfl).and (BT.eq 1 4 0 rfl rfl)))
    (scons f (scons c (fun _ => d))) (fun x y => Ap f x y ∨ (x = c ∧ y = d))
    (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
  · rintro x y (h | ⟨e1, e2⟩)
    · exact ⟨(ha' x).mpr (Or.inl (hf.dom _ _ h).1), (hf.dom _ _ h).2⟩
    · rw [e1, e2]; exact ⟨(ha' c).mpr (Or.inr rfl), hd⟩
  · intro x hx
    rcases (ha' x).mp hx with h | e
    · obtain ⟨y, hy⟩ := hf.tot x h
      exact ⟨y, Or.inl hy⟩
    · exact ⟨d, Or.inr ⟨e, rfl⟩⟩
  · rintro x y y' (h | ⟨e1, e2⟩) (h' | ⟨e1', e2'⟩)
    · exact hf.func _ _ _ h h'
    · exfalso; rw [e1'] at h; exact hc (hf.dom _ _ h).1
    · exfalso; rw [e1] at h'; exact hc (hf.dom _ _ h').1
    · rw [e2, e2']
  · rintro x x' y (h | ⟨e1, e2⟩) (h' | ⟨e1', e2'⟩)
    · exact hf.inj _ _ _ h h'
    · exfalso; rw [e2'] at h; exact hd' _ h
    · exfalso; rw [e2] at h'; exact hd' _ h'
    · rw [e1, e1']

/-- If the universe is finite, any two objects are comparable. -/
theorem comparable (hfin : ¬UnivInfinite (Mem (M := M))) (a b : M) : Le a b ∨ Le b a := by
  refine fin_ind hfin (t := 0) (Γ := []) (R := fun v => ∀ b, Le (v 0) b ∨ Le b (v 0))
    (BT.all 1 ((leB.sub [1, 0] 0).or (leB.sub [0, 1] 0))) (fun _ => a) ?_ ?_ a b
  · intro e he b
    exact Or.inl (le_of_sub fun z hz => absurd hz (he z))
  · intro a c a' ih ha' b
    have haa' : Le a a' := le_of_sub fun z hz => (ha' z).mpr (Or.inl hz)
    rcases ih b with h | h
    · by_cases hc : Mem c a
      · refine Or.inl (le_trans (le_of_sub fun z hz => ?_) h)
        rcases (ha' z).mp hz with h' | e
        · exact h'
        · rw [e]; exact hc
      · obtain ⟨f, hf⟩ := h
        by_cases honto : ∀ y, Mem y b → ∃ x, Ap f x y
        · exact Or.inr (le_trans (le_conv hf honto) haa')
        · obtain ⟨d, hd, hd'⟩ : ∃ d, Mem d b ∧ ∀ x, ¬Ap f x d := by
            by_contra hne
            exact honto fun y hy => by
              by_contra hy'
              exact hne ⟨y, hy, fun x hx => hy' ⟨x, hx⟩⟩
          exact Or.inl (le_adjoin hf hc hd hd' ha')
    · exact Or.inr (le_trans h haa')

/-- From an injection of `pow y` into `a` with one more element, an injection of `simg y` into
`a`. -/
theorem surgery {g y a a' b : M} (hg : Inj g (pow y) a')
    (ha' : ∀ z, Mem z a' ↔ Mem z a ∨ z = b) : Le (simg y) a := by
  have hsp : ∀ x, Mem x y → Mem (sing x) (pow y) := fun x hx =>
    mem_pow.mpr ⟨isSet_sing, fun z hz => by rw [mem_sing.mp hz]; exact hx⟩
  by_cases hcase : ∃ x₀, Mem x₀ y ∧ Ap g (sing x₀) b
  · obtain ⟨x₀, hx₀, hgx₀⟩ := hcase
    obtain ⟨t₀, ht₀⟩ := hg.tot emp
      (mem_pow.mpr ⟨isSet_emp, fun z hz => absurd hz (not_mem_emp z)⟩)
    have hne : t₀ ≠ b := fun e => by
      have : emp = sing x₀ := hg.inj _ _ _ ht₀ (by rw [e]; exact hgx₀)
      exact not_mem_emp x₀ (by rw [this]; exact mem_sing.mpr rfl)
    have ht₀a : Mem t₀ a := ((ha' t₀).mp (hg.dom _ _ ht₀).2).resolve_right hne
    refine le_of_rel (t := 1) (Γ := [2, 4, 1, 1])
      ((BT.mem 0 2 1 rfl rfl).and ((((BT.eq 0 4 1 rfl rfl).not).and (apB.sub [3, 0, 1] 1)).or
        ((BT.eq 0 4 1 rfl rfl).and (BT.eq 1 5 1 rfl rfl))))
      (scons (simg y) (scons g (scons (sing x₀) (fun _ => t₀))))
      (fun u t => Mem u (simg y) ∧ ((¬u = sing x₀ ∧ Ap g u t) ∨ (u = sing x₀ ∧ t = t₀)))
      (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
    · rintro u t ⟨hu, (⟨hne', h⟩ | ⟨_, e⟩)⟩
      · refine ⟨hu, ((ha' t).mp (hg.dom _ _ h).2).resolve_right fun e => hne' ?_⟩
        exact hg.inj _ _ _ h (by rw [e]; exact hgx₀)
      · rw [e]; exact ⟨hu, ht₀a⟩
    · intro u hu
      by_cases e : u = sing x₀
      · exact ⟨t₀, hu, Or.inr ⟨e, rfl⟩⟩
      · obtain ⟨x, hx, hux⟩ := mem_simg.mp hu
        obtain ⟨t, ht⟩ := hg.tot _ (hsp x hx)
        exact ⟨t, hu, Or.inl ⟨e, by rw [hux]; exact ht⟩⟩
    · rintro u t t' ⟨_, (⟨hne', h⟩ | ⟨e, e'⟩)⟩ ⟨_, (⟨hne'', h'⟩ | ⟨e2, e2'⟩)⟩
      · exact hg.func _ _ _ h h'
      · exact absurd e2 hne'
      · exact absurd e hne''
      · rw [e', e2']
    · rintro u u' t ⟨hu, (⟨hne', h⟩ | ⟨e, e'⟩)⟩ ⟨hu', (⟨hne'', h'⟩ | ⟨e2, e2'⟩)⟩
      · exact hg.inj _ _ _ h h'
      · exfalso
        rw [e2'] at h
        have hue : u = emp := hg.inj _ _ _ h ht₀
        obtain ⟨x, _, hux⟩ := mem_simg.mp hu
        exact not_mem_emp x (by rw [← hue, hux]; exact mem_sing.mpr rfl)
      · exfalso
        rw [e'] at h'
        have hue : u' = emp := hg.inj _ _ _ h' ht₀
        obtain ⟨x, _, hux⟩ := mem_simg.mp hu'
        exact not_mem_emp x (by rw [← hue, hux]; exact mem_sing.mpr rfl)
      · rw [e, e2]
  · have hcase' : ∀ x₀, Mem x₀ y → ¬Ap g (sing x₀) b := fun x₀ hx₀ h => hcase ⟨x₀, hx₀, h⟩
    refine le_of_rel (t := 1) (Γ := [2, 4]) ((BT.mem 0 2 1 rfl rfl).and (apB.sub [3, 0, 1] 1))
      (scons (simg y) (fun _ => g)) (fun u t => Mem u (simg y) ∧ Ap g u t)
      (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
    · rintro u t ⟨hu, h⟩
      refine ⟨hu, ((ha' t).mp (hg.dom _ _ h).2).resolve_right fun e => ?_⟩
      obtain ⟨x, hx, hux⟩ := mem_simg.mp hu
      exact hcase' x hx (by rw [← e, ← hux]; exact h)
    · intro u hu
      obtain ⟨x, hx, hux⟩ := mem_simg.mp hu
      obtain ⟨t, ht⟩ := hg.tot _ (hsp x hx)
      exact ⟨t, hu, by rw [hux]; exact ht⟩
    · rintro u t t' ⟨_, h⟩ ⟨_, h'⟩
      exact hg.func _ _ _ h h'
    · rintro u u' t ⟨_, h⟩ ⟨_, h'⟩
      exact hg.inj _ _ _ h h'

/-- If the universe is finite, the tower has a last term below any set of singletons with at
least two members. -/
theorem exists_top (hfin : ¬UnivInfinite (Mem (M := M))) {z : M} (hz : Ge2 (simg z)) :
    ∃ (c : Fin 5) (τ : M), Tw c τ ∧ Le τ (simg z) ∧ ∀ e, Ex τ e → ¬Le e (simg z) := by
  by_contra hno
  have hno' : ∀ (c : Fin 5) (τ : M), Tw c τ → Le τ (simg z) → ∃ e, Ex τ e ∧ Le e (simg z) := by
    intro c τ h1 h2
    by_contra h3
    exact hno ⟨c, τ, h1, h2, fun e he hle => h3 ⟨e, he, hle⟩⟩
  have hall : ∀ i a, Tw i a → Le a (simg z) := by
    intro i a ha
    exact tw_ind (Γ := [2]) (Φ := fun _ v => Le (v 0) (v 1)) (fun _ => leB.sub [0, 1] 1)
      (fun _ => simg z) (fun a ha => two_le ha hz)
      (fun i b a hb hle he => by
        obtain ⟨e, he', hle'⟩ := hno' i b hb hle
        exact le_trans (ex_mono he he' (le_refl _)) hle') i a ha
  have hsome := fin_ind hfin (t := 1) (Γ := [2])
    (R := fun v => Sub (v 0) (v 1) → ¬∀ i : Fin 5, ∀ k, Tw i k → Le k (v 0))
    ((subB.sub [0, 1] 1).imp
      ((BT.forallFin (fun i => BT.all 2 ((twB i).imp (leB.sub [0, 1] 1)))).not))
    (fun _ => simg z) ?base ?step (simg z) (fun _ h => h)
  · exact hsome fun i k hk => hall i k hk
  case base =>
    intro e he _ hall'
    have htwo : Two (upr (TT : M) FF) := two_upr (tt_ne_ff hM)
    obtain ⟨x, _, hx, _, _⟩ := ge2_of_le (two_ge2 htwo) (hall' 0 _ (tw_base htwo))
    exact he x hx
  case step =>
    intro a b a' ih ha' hsub hall'
    have hsub' : Sub a (simg z) := fun x hx => hsub x ((ha' x).mpr (Or.inl hx))
    apply ih hsub'
    intro i k hk
    obtain ⟨y, hy⟩ := le_simg_ex (le_trans (hall' i k hk) (le_of_sub hsub))
    have hk' : Tw (i + 1) (pow y) := tw_step hk ⟨y, hy, eqv_refl _⟩
    obtain ⟨g, hg⟩ := hall' (i + 1) (pow y) hk'
    exact le_trans hy.1 (surgery hg ha')

/-! ### The two bounds -/

/-- Sets are objects: the power set of the set of double singletons injects into the set of
double singletons. -/
theorem lemA : Le (pow (simg (simg (univ : M)))) (simg (simg (univ : M))) :=
  le_trans (pow_simg_le _) (le_trans (le_simg (pow_simg_le _))
    (le_simg (le_simg (le_of_sub fun z _ => mem_univ z))))

/-- Objects are functions, and a function is determined by its graph: the set of double
singletons injects into the third power set of the universe. -/
theorem lemB : Le (simg (simg (univ : M))) (pow (pow (pow (univ : M)))) := by
  have hgraph : ∀ f : M, ∃ g : M, IsSet g ∧ ∀ p, Mem p g ↔ ∃ x y, p = kp x y ∧ f ⬝ x = y :=
    fun f => (BT.ex (Γ := [2, 1]) 0 (BT.ex 0 ((kpB.sub [2, 1, 0] 0).and
      (BT.app 3 1 0 0 rfl rfl rfl)))).set (fun _ => f)
  refine le_of_rel (t := 3) (Γ := [])
    (BT.ex 1 ((BT.ex 2 ((singB.sub [0, 1] 1).and (singB.sub [2, 0] 2))).and
      ((BT.isSet 2 2 rfl).and (BT.all 2 ((BT.mem 0 3 2 rfl rfl).iff
        (BT.ex 0 (BT.ex 0 ((kpB.sub [2, 1, 0] 0).and (BT.app 3 1 0 0 rfl rfl rfl)))))))))
    (fun _ => Classical.arbitrary M)
    (fun u g => ∃ f, (∃ t, t = sing f ∧ u = sing t) ∧ IsSet g ∧
      ∀ p, Mem p g ↔ ∃ x y, p = kp x y ∧ f ⬝ x = y)
    (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
  · rintro u g ⟨f, ⟨t, rfl, rfl⟩, hg, hmem⟩
    refine ⟨mem_simg_sing.mpr (mem_simg_sing.mpr (mem_univ f)),
      mem_pow.mpr ⟨hg, fun p hp => ?_⟩⟩
    obtain ⟨x, y, rfl, -⟩ := (hmem p).mp hp
    refine mem_pow.mpr ⟨isSet_upr, fun r hr => ?_⟩
    rcases mem_upr.mp hr with rfl | rfl
    · exact mem_pow.mpr ⟨isSet_sing, fun z _ => mem_univ z⟩
    · exact mem_pow.mpr ⟨isSet_upr, fun z _ => mem_univ z⟩
  · intro u hu
    obtain ⟨t, ht, rfl⟩ := mem_simg.mp hu
    obtain ⟨f, -, rfl⟩ := mem_simg.mp ht
    obtain ⟨g, hg, hmem⟩ := hgraph f
    exact ⟨g, f, ⟨_, rfl, rfl⟩, hg, hmem⟩
  · rintro u g g' ⟨f, ⟨t, rfl, rfl⟩, hg, hmem⟩ ⟨f', ⟨t', rfl, e⟩, hg', hmem'⟩
    obtain rfl := sing_inj (sing_inj e)
    exact set_ext hg hg' fun p => (hmem p).trans (hmem' p).symm
  · rintro u u' g ⟨f, ⟨t, rfl, rfl⟩, hg, hmem⟩ ⟨f', ⟨t', rfl, rfl⟩, hg', hmem'⟩
    have : f = f' := fn_ext hM fun x => by
      obtain ⟨x', y', e, h⟩ := (hmem' (kp x (f ⬝ x))).mp ((hmem _).mpr ⟨x, _, rfl, rfl⟩)
      obtain ⟨rfl, rfl⟩ := kp_inj e
      exact h.symm
    rw [this]

/-! ### The universe is not finite -/

/-- **The universe of a model of FunctionNF is not finite.** -/
theorem univInfinite : UnivInfinite (Mem (M := M)) := by
  by_contra hfin
  have ne : ∀ c : Fin 5, c + 1 ≠ c ∧ c + 1 + 1 ≠ c ∧ c + 1 + 1 + 1 ≠ c ∧ c + 1 + 1 + 1 + 1 ≠ c := by
    decide
  have hw2 : Ge2 (simg (simg (univ : M))) :=
    ⟨sing (sing TT), sing (sing FF), mem_simg_sing.mpr (mem_simg_sing.mpr (mem_univ _)),
      mem_simg_sing.mpr (mem_simg_sing.mpr (mem_univ _)),
      fun e => tt_ne_ff hM (sing_inj (sing_inj e))⟩
  obtain ⟨c, τ, hτ, hτw, htop⟩ := exists_top hfin hw2
  obtain ⟨y, hy⟩ := le_simg_ex hτw
  have h1 : ¬Le (pow y) (simg (simg univ)) := htop _ ⟨y, hy, eqv_refl _⟩
  have hTP : Tw (c + 1) (pow τ) := tw_step (tw_simg hτ) (ex_self τ)
  have hPw : Le (pow τ) (simg (simg univ)) := le_trans (le_pow hτw) lemA
  have hPτ : Le (pow τ) τ := by
    rcases tw_D hτ hTP with h | ⟨e, he, hle⟩
    · exact h
    · exact absurd (le_trans hle hPw) (htop e he)
  have hAB : Le (simg (simg (simg (pow τ)))) (simg (simg (simg τ))) :=
    le_simg (le_simg (le_simg hPτ))
  have hB : Tw c (simg (simg (simg τ))) := tw_simg (tw_simg (tw_simg hτ))
  have hA : Tw (c + 1) (simg (simg (simg (pow τ)))) := tw_simg (tw_simg (tw_simg hTP))
  have h2 : ¬Le (pow τ) (simg (simg (simg univ))) := fun h =>
    h1 (le_of_simg (le_trans (simg_pow_le y) (le_trans (le_pow hy.2) h)))
  have h3 : Le (simg (simg (simg univ))) (pow τ) := (comparable hfin _ _).resolve_right h2
  have s3 : ∀ a : M, Le (simg (simg (simg (pow a)))) (pow (simg (simg (simg a)))) := fun a =>
    le_trans (le_simg (le_simg (simg_pow_le a)))
      (le_trans (le_simg (simg_pow_le (simg a))) (simg_pow_le (simg (simg a))))
  have k1 : Le (simg (simg (simg (pow univ)))) (pow (pow τ)) := le_trans (s3 _) (le_pow h3)
  have k2 : Le (simg (simg (simg (pow (pow univ))))) (pow (pow (pow τ))) :=
    le_trans (s3 _) (le_pow k1)
  have k3 : Le (simg (simg (simg (pow (pow (pow univ)))))) (pow (pow (pow (pow τ)))) :=
    le_trans (s3 _) (le_pow k2)
  have hBC : Le (simg (simg (simg τ))) (pow (pow (pow (pow τ)))) :=
    le_trans (le_simg (le_simg (le_simg hτw)))
      (le_trans (le_simg (le_simg (le_simg lemB))) k3)
  have x1 : Ex (simg (simg (simg (pow τ)))) (pow (simg (simg (pow τ)))) := ex_self _
  have hE1 : Tw (c + 1 + 1) (pow (simg (simg (pow τ)))) := tw_step hA x1
  have x2 : Ex (pow (simg (simg (pow τ)))) (pow (simg (pow (pow τ)))) :=
    ⟨simg (pow (pow τ)), ⟨le_trans (pow_simg_le _) (le_simg (pow_simg_le _)),
      le_trans (le_simg (simg_pow_le _)) (simg_pow_le _)⟩, eqv_refl _⟩
  have hE2 : Tw (c + 1 + 1 + 1) (pow (simg (pow (pow τ)))) := tw_step hE1 x2
  have x3 : Ex (pow (simg (pow (pow τ)))) (pow (pow (pow (pow τ)))) :=
    ⟨pow (pow (pow τ)), ⟨pow_simg_le _, simg_pow_le _⟩, eqv_refl _⟩
  have hC : Tw (c + 1 + 1 + 1 + 1) (pow (pow (pow (pow τ)))) := tw_step hE2 x3
  rcases tw_D hA hB with h | ⟨e, he, hle⟩
  · exact (ne c).1 (tw_res hB hA ⟨h, hAB⟩)
  · have hE1B := le_trans (ex_mono x1 he (le_refl _)) hle
    rcases tw_D hE1 hB with h | ⟨e, he, hle⟩
    · exact (ne c).2.1 (tw_res hB hE1 ⟨h, hE1B⟩)
    · have hE2B := le_trans (ex_mono x2 he (le_refl _)) hle
      rcases tw_D hE2 hB with h | ⟨e, he, hle⟩
      · exact (ne c).2.2.1 (tw_res hB hE2 ⟨h, hE2B⟩)
      · have hCB := le_trans (ex_mono x3 he (le_refl _)) hle
        exact (ne c).2.2.2 (tw_res hB hC ⟨hBC, hCB⟩)

end

end FFL.FirstOrder.FNF
