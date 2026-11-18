import FnBool

set_option autoImplicit false

/-!
# Inside a model of FunctionNF: sets, injections and Cantor's theorem

Fix a model `M` of `𝗙𝗡𝗙`. `Mem` is the membership relation of `FnBool.lean`.

* Operations on sets: `emp`, `univ`, `sing x` (the singleton), `upr x y` (the unordered pair),
  `kp x y` (the Kuratowski pair), `simg a` (the set of singletons of the members of `a`),
  `pow a` (the set of sets included in `a`).
* `Inj f a b`: the set `f` of Kuratowski pairs is an injection of `a` into `b`.
  `Le a b`: there is one. `Eqv a b`: `Le a b` and `Le b a`.
* `le_of_rel`: a relation with a truth-value term that is total on `a`, single-valued and
  injective gives `Le a b`. Every injection below is made with it.
* `le_simg`, `le_of_simg`, `le_pow`, `simg_pow_le`, `pow_simg_le`, `le_simg_ex`, `le_conv`.
* `cantor`: there is no injection of `pow y` into `simg y`.
-/

namespace FFL.FirstOrder.FNF

open JensenNFU.TFm (scons scons_zero scons_succ)

variable {M : Type} [s : Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

local infixl:70 " ⬝ " => App

/-- The `i`-th entry of a list of indices. -/
def nth : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, i + 1 => nth l i

/-- Exchange the first two variables and skip the third. -/
def swp : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | i + 2 => i + 3

noncomputable section

namespace BT

variable {Γ Γ' : List ℕ} {R S : (ℕ → M) → Prop}

/-- Substitution of variables given by a list of indices; the side condition on the levels is
checked by computation. -/
def sub (p : BT Γ R) (l : List ℕ) (c : ℕ)
    (h : (List.range Γ.length).all (fun i => Γ'[nth l i]? == some (Γ.getD i 0 + c)) = true := by
      rfl) :
    BT Γ' (fun v => R (fun i => v (nth l i))) :=
  p.comp (nth l) c (fun i hi => by
    have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
    rw [List.getD_eq_getElem _ _ hi] at this
    exact beq_iff_eq.mp this)

/-- The true relation. -/
def tru : BT Γ (fun _ : ℕ → M => True) :=
  ofOk 0 (fun _ _ => .tt) ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ env _ _ _ _ => by
    show ev LTm.tt env = bool True
    rw [ev_tt, bool_true trivial]⟩

/-- A relation that does not depend on the variables. -/
def const (p : Prop) : BT Γ (fun _ : ℕ → M => p) :=
  haveI := Classical.propDecidable p
  if h : p then tru.congr (fun _ => ⟨fun _ => h, fun _ => trivial⟩)
  else (tru.not).congr (fun _ => ⟨fun h' => absurd trivial h', fun h' => absurd h' h⟩)

/-- A finite conjunction. -/
def forallFin : ∀ {n : ℕ} {R : Fin n → (ℕ → M) → Prop}, (∀ i, BT Γ (R i)) →
    BT Γ (fun v => ∀ i, R i v)
  | 0, _, _ => tru.congr (fun _ => ⟨fun _ i => i.elim0, fun _ => trivial⟩)
  | _ + 1, _, p => ((p 0).and (forallFin (fun i => p i.succ))).congr (fun _ =>
      ⟨fun h i => by
        refine Fin.cases ?_ ?_ i
        · exact h.1
        · exact h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩)

end BT

theorem eq_set_iff {y z : M} (hz : IsSet z) : y = z ↔ IsSet y ∧ ∀ x, Mem x y ↔ Mem x z :=
  ⟨fun h => by subst h; exact ⟨hz, fun _ => Iff.rfl⟩, fun h => set_ext h.1 hz h.2⟩

/-- `vᵢ = f v`, for an operation `f` whose values are sets with a definable membership. -/
def BT.setEq {Γ : List ℕ} (i a : ℕ) (hi : Γ[i]? = some (a + 1)) {S : (ℕ → M) → Prop}
    (p : BT (a :: Γ) S) (f : (ℕ → M) → M) (hf : ∀ v, IsSet (f v))
    (hmem : ∀ v z, Mem z (f v) ↔ S (scons z v)) : BT Γ (fun v => v i = f v) :=
  BT.congr ((BT.isSet i a hi).and (BT.all a ((BT.mem 0 (i + 1) a rfl
    (by rw [List.getElem?_cons_succ]; exact hi)).iff p)))
    fun v => ((eq_set_iff (hf v)).trans
      (and_congr Iff.rfl (forall_congr' fun z => iff_congr Iff.rfl (hmem v z)))).symm

/-! ### The operations -/

theorem exists_emp : ∃ y : M, IsSet y ∧ ∀ x, Mem x y ↔ False :=
  (BT.const (Γ := [0]) False).set (fun _ => Classical.arbitrary M)

/-- The empty set. -/
def emp : M := Classical.choose (exists_emp (M := M))

theorem isSet_emp : IsSet (emp : M) := (Classical.choose_spec exists_emp).1

theorem not_mem_emp (x : M) : ¬Mem x (emp : M) :=
  fun h => ((Classical.choose_spec exists_emp).2 x).mp h

theorem exists_univ : ∃ y : M, IsSet y ∧ ∀ x, Mem x y ↔ True :=
  (BT.tru (Γ := [0])).set (fun _ => Classical.arbitrary M)

/-- The universal set. -/
def univ : M := Classical.choose (exists_univ (M := M))

theorem isSet_univ : IsSet (univ : M) := (Classical.choose_spec exists_univ).1

theorem mem_univ (x : M) : Mem x (univ : M) := ((Classical.choose_spec exists_univ).2 x).mpr trivial

theorem exists_sing (x : M) : ∃ y : M, IsSet y ∧ ∀ z, Mem z y ↔ z = x :=
  (BT.eq (Γ := [0, 0]) 0 1 0 rfl rfl).set (fun _ => x)

/-- The singleton. -/
def sing (x : M) : M := Classical.choose (exists_sing x)

theorem isSet_sing {x : M} : IsSet (sing x) := (Classical.choose_spec (exists_sing x)).1

theorem mem_sing {x z : M} : Mem z (sing x) ↔ z = x := (Classical.choose_spec (exists_sing x)).2 z

theorem sing_inj {x y : M} (h : sing x = sing y) : x = y := by
  have : Mem x (sing x) := mem_sing.mpr rfl
  rw [h] at this
  exact mem_sing.mp this

theorem exists_upr (x y : M) : ∃ u : M, IsSet u ∧ ∀ z, Mem z u ↔ z = x ∨ z = y :=
  ((BT.eq (Γ := [0, 0, 0]) 0 1 0 rfl rfl).or (BT.eq 0 2 0 rfl rfl)).set (scons x (fun _ => y))

/-- The unordered pair. -/
def upr (x y : M) : M := Classical.choose (exists_upr x y)

theorem isSet_upr {x y : M} : IsSet (upr x y) := (Classical.choose_spec (exists_upr x y)).1

theorem mem_upr {x y z : M} : Mem z (upr x y) ↔ z = x ∨ z = y :=
  (Classical.choose_spec (exists_upr x y)).2 z

/-- The Kuratowski pair. -/
def kp (x y : M) : M := upr (sing x) (upr x y)

theorem kp_inj {x y x' y' : M} (h : kp x y = kp x' y') : x = x' ∧ y = y' := by
  have key : ∀ x y y' : M, Mem (upr x y) (kp x y') → y = x ∨ y = y' := by
    intro x y y' h
    have hy : Mem y (upr x y) := mem_upr.mpr (Or.inr rfl)
    rcases mem_upr.mp h with e | e
    · rw [e] at hy; exact Or.inl (mem_sing.mp hy)
    · rw [e] at hy; exact mem_upr.mp hy
  have hx : x = x' := by
    have h1 : Mem (sing x) (kp x' y') := h ▸ (mem_upr.mpr (Or.inl rfl) : Mem (sing x) (kp x y))
    rcases mem_upr.mp h1 with e | e
    · exact sing_inj e
    · have : Mem x' (sing x) := e ▸ (mem_upr.mpr (Or.inl rfl) : Mem x' (upr x' y'))
      exact (mem_sing.mp this).symm
  subst hx
  refine ⟨rfl, ?_⟩
  have h1 : y = x ∨ y = y' := key x y y' (h ▸ (mem_upr.mpr (Or.inr rfl) : Mem (upr x y) (kp x y)))
  have h2 : y' = x ∨ y' = y :=
    key x y' y (h.symm ▸ (mem_upr.mpr (Or.inr rfl) : Mem (upr x y') (kp x y')))
  rcases h1 with e | e
  · rcases h2 with e' | e'
    · exact e.trans e'.symm
    · exact e'.symm
  · exact e

/-- `a` is included in `b`. -/
def Sub (a b : M) : Prop := ∀ z, Mem z a → Mem z b

def singB : BT [1, 0] (fun v : ℕ → M => v 0 = sing (v 1)) :=
  BT.setEq 0 0 rfl (BT.eq 0 2 0 rfl rfl) (fun v => sing (v 1)) (fun _ => isSet_sing)
    (fun _ _ => mem_sing)

def uprB : BT [1, 0, 0] (fun v : ℕ → M => v 0 = upr (v 1) (v 2)) :=
  BT.setEq 0 0 rfl ((BT.eq 0 2 0 rfl rfl).or (BT.eq 0 3 0 rfl rfl)) (fun v => upr (v 1) (v 2))
    (fun _ => isSet_upr) (fun _ _ => mem_upr)

def kpB : BT [2, 0, 0] (fun v : ℕ → M => v 0 = kp (v 1) (v 2)) :=
  BT.congr (BT.ex 1 (BT.ex 1 ((singB.sub [0, 3] 0).and
    ((uprB.sub [1, 3, 4] 0).and (uprB.sub [2, 0, 1] 1)))))
    fun v => ⟨fun ⟨u, s', (h1 : s' = sing (v 1)), (h2 : u = upr (v 1) (v 2)),
      (h3 : v 0 = upr s' u)⟩ => by subst h1 h2; exact h3, fun h => ⟨_, _, rfl, rfl, h⟩⟩

def subB : BT [1, 1] (fun v : ℕ → M => Sub (v 0) (v 1)) :=
  BT.congr (BT.all 0 ((BT.mem 0 1 0 rfl rfl).imp (BT.mem 0 2 0 rfl rfl))) fun _ => Iff.rfl

theorem exists_simg (a : M) : ∃ b : M, IsSet b ∧ ∀ z, Mem z b ↔ ∃ x, Mem x a ∧ z = sing x :=
  (BT.ex (Γ := [1, 1]) 0 ((BT.mem 0 2 0 rfl rfl).and (singB.sub [1, 0] 0))).set (fun _ => a)

/-- The set of the singletons of the members of `a`. -/
def simg (a : M) : M := Classical.choose (exists_simg a)

theorem isSet_simg {a : M} : IsSet (simg a) := (Classical.choose_spec (exists_simg a)).1

theorem mem_simg {a z : M} : Mem z (simg a) ↔ ∃ x, Mem x a ∧ z = sing x :=
  (Classical.choose_spec (exists_simg a)).2 z

theorem mem_simg_sing {a x : M} : Mem (sing x) (simg a) ↔ Mem x a :=
  ⟨fun h => by obtain ⟨x', hx', e⟩ := mem_simg.mp h; rwa [sing_inj e],
    fun h => mem_simg.mpr ⟨x, h, rfl⟩⟩

theorem sub_simg {a b : M} (h : Sub a b) : Sub (simg a) (simg b) := fun z hz => by
  obtain ⟨x, hx, rfl⟩ := mem_simg.mp hz
  exact mem_simg_sing.mpr (h x hx)

theorem simg_inj {a b : M} (ha : IsSet a) (hb : IsSet b) (h : simg a = simg b) : a = b :=
  set_ext ha hb fun z => by rw [← mem_simg_sing, h, mem_simg_sing]

theorem exists_pow (a : M) : ∃ b : M, IsSet b ∧ ∀ z, Mem z b ↔ IsSet z ∧ Sub z a :=
  ((BT.isSet (Γ := [1, 1]) 0 0 rfl).and subB).set (fun _ => a)

/-- The set of the sets included in `a`. -/
def pow (a : M) : M := Classical.choose (exists_pow a)

theorem isSet_pow {a : M} : IsSet (pow a) := (Classical.choose_spec (exists_pow a)).1

theorem mem_pow {a z : M} : Mem z (pow a) ↔ IsSet z ∧ Sub z a :=
  (Classical.choose_spec (exists_pow a)).2 z

def simgB : BT [2, 1] (fun v : ℕ → M => v 0 = simg (v 1)) :=
  BT.setEq 0 1 rfl (BT.ex 0 ((BT.mem 0 3 0 rfl rfl).and (singB.sub [1, 0] 0)))
    (fun v => simg (v 1)) (fun _ => isSet_simg) (fun _ _ => mem_simg)

def powB : BT [2, 1] (fun v : ℕ → M => v 0 = pow (v 1)) :=
  BT.setEq 0 1 rfl ((BT.isSet 0 0 rfl).and (subB.sub [0, 2] 0))
    (fun v => pow (v 1)) (fun _ => isSet_pow) (fun _ _ => mem_pow)

/-! ### Injections -/

/-- The pair of `x` and `y` is in `f`. -/
def Ap (f x y : M) : Prop := Mem (kp x y) f

def apB : BT [3, 0, 0] (fun v : ℕ → M => Ap (v 0) (v 1) (v 2)) :=
  BT.congr (BT.ex 2 ((kpB.sub [0, 2, 3] 0).and (BT.mem 0 1 2 rfl rfl)))
    fun v => ⟨fun ⟨p, (h1 : p = kp (v 1) (v 2)), (h2 : Mem p (v 0))⟩ => by subst h1; exact h2,
      fun h => ⟨_, rfl, h⟩⟩

/-- `f` is an injection of `a` into `b`. -/
structure Inj (f a b : M) : Prop where
  dom : ∀ x y, Ap f x y → Mem x a ∧ Mem y b
  tot : ∀ x, Mem x a → ∃ y, Ap f x y
  func : ∀ x y y', Ap f x y → Ap f x y' → y = y'
  inj : ∀ x x' y, Ap f x y → Ap f x' y → x = x'

/-- There is an injection of `a` into `b`. -/
def Le (a b : M) : Prop := ∃ f, Inj f a b

/-- `a` and `b` inject into each other. -/
def Eqv (a b : M) : Prop := Le a b ∧ Le b a

def injB : BT [3, 1, 1] (fun v : ℕ → M => Inj (v 0) (v 1) (v 2)) :=
  BT.congr
    ((BT.all 0 (BT.all 0 ((apB.sub [2, 1, 0] 0).imp
        ((BT.mem 1 3 0 rfl rfl).and (BT.mem 0 4 0 rfl rfl))))).and
      ((BT.all 0 ((BT.mem 0 2 0 rfl rfl).imp (BT.ex 0 (apB.sub [2, 1, 0] 0)))).and
        ((BT.all 0 (BT.all 0 (BT.all 0 ((apB.sub [3, 2, 1] 0).imp
            ((apB.sub [3, 2, 0] 0).imp (BT.eq 1 0 0 rfl rfl)))))).and
          (BT.all 0 (BT.all 0 (BT.all 0 ((apB.sub [3, 2, 0] 0).imp
            ((apB.sub [3, 1, 0] 0).imp (BT.eq 2 1 0 rfl rfl)))))))))
    fun _ => ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun h => ⟨h.dom, h.tot, h.func, h.inj⟩⟩

def leB : BT [1, 1] (fun v : ℕ → M => Le (v 0) (v 1)) :=
  BT.congr (BT.ex 3 injB) fun _ => Iff.rfl

def eqvB : BT [1, 1] (fun v : ℕ → M => Eqv (v 0) (v 1)) :=
  BT.congr (leB.and (leB.sub [1, 0] 0)) fun _ => Iff.rfl

/-- **Making an injection.** A relation with a truth-value term that is total on `a`, has values
in `b`, and is single-valued and injective, gives an injection of `a` into `b`. -/
theorem le_of_rel {t : ℕ} {Γ : List ℕ} {R : (ℕ → M) → Prop} (p : BT (t :: t :: Γ) R) (q : ℕ → M)
    {a b : M} (F : M → M → Prop) (hF : ∀ x y, R (scons x (scons y q)) ↔ F x y)
    (hdom : ∀ x y, F x y → Mem x a ∧ Mem y b)
    (htot : ∀ x, Mem x a → ∃ y, F x y)
    (hfun : ∀ x y y', F x y → F x y' → y = y')
    (hinj : ∀ x x' y, F x y → F x' y → x = x') : Le a b := by
  obtain ⟨g, -, hg'⟩ :=
    (BT.ex (Γ := (t + 2) :: Γ) t (BT.ex t ((kpB.comp (nth [2, 1, 0]) t (fun i hi => by
        match i, hi with
        | 0, _ => show some (t + 2) = some (2 + t); rw [Nat.add_comm]
        | 1, _ => show some t = some (0 + t); rw [Nat.zero_add]
        | 2, _ => show some t = some (0 + t); rw [Nat.zero_add]
        | i + 3, hi => exact absurd hi (by simp))).and
      (p.comp swp 0 (fun i hi => by
        match i, hi with
        | 0, _ => rfl
        | 1, _ => rfl
        | i + 2, hi =>
          have hi' : i < Γ.length := by simpa using hi
          show Γ[i]? = some (Γ[i] + 0)
          rw [List.getElem?_eq_getElem hi']; rfl))))).set q
  have e : ∀ (x y pr : M), (fun i => scons y (scons x (scons pr q)) (swp i)) =
      scons x (scons y q) := by
    intro x y pr
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | i + 2 => rfl
  have key : ∀ x y, Ap g x y ↔ F x y := by
    intro x y
    refine (hg' (kp x y)).trans ⟨?_, fun h => ?_⟩
    · rintro ⟨x', y', (h1 : kp x y = kp x' y'),
        (h2 : R (fun i => scons y' (scons x' (scons (kp x y) q)) (swp i)))⟩
      obtain ⟨rfl, rfl⟩ := kp_inj h1
      rw [e] at h2
      exact (hF x y).mp h2
    · refine ⟨x, y, rfl, ?_⟩
      show R (fun i => scons y (scons x (scons (kp x y) q)) (swp i))
      rw [e]
      exact (hF x y).mpr h
  exact ⟨g, ⟨fun x y h => hdom x y ((key x y).mp h),
    fun x hx => (htot x hx).imp fun y hy => (key x y).mpr hy,
    fun x y y' h h' => hfun x y y' ((key x y).mp h) ((key x y').mp h'),
    fun x x' y h h' => hinj x x' y ((key x y).mp h) ((key x' y).mp h')⟩⟩

theorem le_of_sub {a b : M} (h : Sub a b) : Le a b :=
  le_of_rel (t := 0) (Γ := [1]) ((BT.eq 0 1 0 rfl rfl).and (BT.mem 0 2 0 rfl rfl)) (fun _ => a)
    (fun x y => x = y ∧ Mem x a) (fun _ _ => Iff.rfl)
    (fun x y ⟨e, hx⟩ => ⟨hx, h y (e ▸ hx)⟩)
    (fun x hx => ⟨x, rfl, hx⟩)
    (fun x y y' ⟨e, _⟩ ⟨e', _⟩ => e.symm.trans e')
    (fun x x' y ⟨e, _⟩ ⟨e', _⟩ => e.trans e'.symm)

theorem le_refl (a : M) : Le a a := le_of_sub fun _ h => h

theorem le_trans {a b c : M} (h1 : Le a b) (h2 : Le b c) : Le a c := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  refine le_of_rel (t := 0) (Γ := [3, 3])
    (BT.ex 0 ((apB.sub [3, 1, 0] 0).and (apB.sub [4, 0, 2] 0))) (scons f (fun _ => g))
    (fun x z => ∃ y, Ap f x y ∧ Ap g y z) (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
  · rintro x z ⟨y, h, h'⟩
    exact ⟨(hf.dom _ _ h).1, (hg.dom _ _ h').2⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hf.tot x hx
    obtain ⟨z, hz⟩ := hg.tot y (hf.dom _ _ hy).2
    exact ⟨z, y, hy, hz⟩
  · rintro x z z' ⟨y, h, h'⟩ ⟨y', k, k'⟩
    obtain rfl := hf.func _ _ _ h k
    exact hg.func _ _ _ h' k'
  · rintro x x' z ⟨y, h, h'⟩ ⟨y', k, k'⟩
    obtain rfl := hg.inj _ _ _ h' k'
    exact hf.inj _ _ _ h k

theorem eqv_refl (a : M) : Eqv a a := ⟨le_refl a, le_refl a⟩

theorem Eqv.symm {a b : M} (h : Eqv a b) : Eqv b a := ⟨h.2, h.1⟩

theorem Eqv.trans {a b c : M} (h : Eqv a b) (h' : Eqv b c) : Eqv a c :=
  ⟨le_trans h.1 h'.1, le_trans h'.2 h.2⟩

/-- The converse of an injection onto `b`. -/
theorem le_conv {f a b : M} (hf : Inj f a b) (honto : ∀ y, Mem y b → ∃ x, Ap f x y) : Le b a :=
  le_of_rel (t := 0) (Γ := [3]) (apB.sub [2, 1, 0] 0) (fun _ => f) (fun y x => Ap f x y)
    (fun _ _ => Iff.rfl)
    (fun y x h => ⟨(hf.dom _ _ h).2, (hf.dom _ _ h).1⟩) honto
    (fun y x x' h h' => hf.inj _ _ _ h h') (fun y y' x h h' => hf.func _ _ _ h h')

theorem le_simg {a b : M} (h : Le a b) : Le (simg a) (simg b) := by
  obtain ⟨f, hf⟩ := h
  refine le_of_rel (t := 1) (Γ := [3])
    (BT.ex 0 (BT.ex 0 ((apB.sub [4, 1, 0] 0).and
      ((singB.sub [2, 1] 0).and (singB.sub [3, 0] 0)))))
    (fun _ => f) (fun u t => ∃ x y, Ap f x y ∧ u = sing x ∧ t = sing y) (fun _ _ => Iff.rfl)
    ?_ ?_ ?_ ?_
  · rintro u t ⟨x, y, h, rfl, rfl⟩
    exact ⟨mem_simg_sing.mpr (hf.dom _ _ h).1, mem_simg_sing.mpr (hf.dom _ _ h).2⟩
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := mem_simg.mp hu
    obtain ⟨y, hy⟩ := hf.tot x hx
    exact ⟨sing y, x, y, hy, rfl, rfl⟩
  · rintro u t t' ⟨x, y, h, rfl, rfl⟩ ⟨x', y', h', e, rfl⟩
    obtain rfl := sing_inj e
    rw [hf.func _ _ _ h h']
  · rintro u u' t ⟨x, y, h, rfl, rfl⟩ ⟨x', y', h', rfl, e⟩
    obtain rfl := sing_inj e
    rw [hf.inj _ _ _ h h']

theorem le_of_simg {a b : M} (h : Le (simg a) (simg b)) : Le a b := by
  obtain ⟨f, hf⟩ := h
  refine le_of_rel (t := 0) (Γ := [4])
    (BT.ex 1 (BT.ex 1 ((apB.sub [4, 1, 0] 1).and
      ((singB.sub [1, 2] 0).and (singB.sub [0, 3] 0)))))
    (fun _ => f) (fun x y => ∃ u t, Ap f u t ∧ u = sing x ∧ t = sing y) (fun _ _ => Iff.rfl)
    ?_ ?_ ?_ ?_
  · rintro x y ⟨u, t, h, rfl, rfl⟩
    exact ⟨mem_simg_sing.mp (hf.dom _ _ h).1, mem_simg_sing.mp (hf.dom _ _ h).2⟩
  · intro x hx
    obtain ⟨t, ht⟩ := hf.tot (sing x) (mem_simg_sing.mpr hx)
    obtain ⟨y, -, rfl⟩ := mem_simg.mp (hf.dom _ _ ht).2
    exact ⟨y, sing x, sing y, ht, rfl, rfl⟩
  · rintro x y y' ⟨u, t, h, rfl, rfl⟩ ⟨u', t', h', rfl, rfl⟩
    exact sing_inj (hf.func _ _ _ h h')
  · rintro x x' y ⟨u, t, h, rfl, rfl⟩ ⟨u', t', h', rfl, rfl⟩
    exact sing_inj (hf.inj _ _ _ h h')

theorem le_pow {a b : M} (h : Le a b) : Le (pow a) (pow b) := by
  obtain ⟨f, hf⟩ := h
  refine le_of_rel (t := 1) (Γ := [1, 3])
    (((BT.isSet 0 0 rfl).and (subB.sub [0, 2] 0)).and ((BT.isSet 1 0 rfl).and
      (BT.all 0 ((BT.mem 0 2 0 rfl rfl).iff
        (BT.ex 0 ((BT.mem 0 2 0 rfl rfl).and (apB.sub [5, 0, 1] 0)))))))
    (scons a (fun _ => f))
    (fun u t => (IsSet u ∧ Sub u a) ∧ IsSet t ∧ ∀ y, Mem y t ↔ ∃ x, Mem x u ∧ Ap f x y)
    (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
  · rintro u t ⟨hu, ht, hmem⟩
    refine ⟨mem_pow.mpr hu, mem_pow.mpr ⟨ht, fun y hy => ?_⟩⟩
    obtain ⟨x, _, hxy⟩ := (hmem y).mp hy
    exact (hf.dom _ _ hxy).2
  · intro u hu
    obtain ⟨t, ht, hmem⟩ := (BT.ex (Γ := [0, 1, 3]) 0
      ((BT.mem 0 2 0 rfl rfl).and (apB.sub [3, 0, 1] 0))).set (scons u (fun _ => f))
    exact ⟨t, mem_pow.mp hu, ht, hmem⟩
  · rintro u t t' ⟨_, ht, h⟩ ⟨_, ht', h'⟩
    exact set_ext ht ht' fun y => (h y).trans (h' y).symm
  · rintro u u' t ⟨⟨hu, hua⟩, _, h⟩ ⟨⟨hu', hua'⟩, _, h'⟩
    refine set_ext hu hu' fun z => ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨y, hy⟩ := hf.tot z (hua z hz)
      obtain ⟨x, hx, hxy⟩ := (h' y).mp ((h y).mpr ⟨z, hz, hy⟩)
      rwa [hf.inj _ _ _ hy hxy]
    · obtain ⟨y, hy⟩ := hf.tot z (hua' z hz)
      obtain ⟨x, hx, hxy⟩ := (h y).mp ((h' y).mpr ⟨z, hz, hy⟩)
      rwa [hf.inj _ _ _ hy hxy]

theorem simg_pow_le (a : M) : Le (simg (pow a)) (pow (simg a)) := by
  refine le_of_rel (t := 2) (Γ := [1])
    (BT.ex 1 (((BT.isSet 0 0 rfl).and (subB.sub [0, 3] 0)).and
      ((singB.sub [1, 0] 1).and (simgB.sub [2, 0] 0))))
    (fun _ => a) (fun u t => ∃ z, (IsSet z ∧ Sub z a) ∧ u = sing z ∧ t = simg z)
    (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
  · rintro u t ⟨z, hz, rfl, rfl⟩
    exact ⟨mem_simg_sing.mpr (mem_pow.mpr hz), mem_pow.mpr ⟨isSet_simg, sub_simg hz.2⟩⟩
  · intro u hu
    obtain ⟨z, hz, rfl⟩ := mem_simg.mp hu
    exact ⟨simg z, z, mem_pow.mp hz, rfl, rfl⟩
  · rintro u t t' ⟨z, _, rfl, rfl⟩ ⟨z', _, e, rfl⟩
    rw [sing_inj e]
  · rintro u u' t ⟨z, hz, rfl, rfl⟩ ⟨z', hz', rfl, e⟩
    rw [simg_inj hz.1 hz'.1 e]

theorem pow_simg_le (a : M) : Le (pow (simg a)) (simg (pow a)) := by
  refine le_of_rel (t := 2) (Γ := [1])
    (BT.ex 1 (((BT.isSet 0 0 rfl).and (subB.sub [0, 3] 0)).and
      ((singB.sub [2, 0] 1).and (simgB.sub [1, 0] 0))))
    (fun _ => a) (fun t u => ∃ z, (IsSet z ∧ Sub z a) ∧ u = sing z ∧ t = simg z)
    (fun _ _ => Iff.rfl) ?_ ?_ ?_ ?_
  · rintro t u ⟨z, hz, rfl, rfl⟩
    exact ⟨mem_pow.mpr ⟨isSet_simg, sub_simg hz.2⟩, mem_simg_sing.mpr (mem_pow.mpr hz)⟩
  · intro t ht
    obtain ⟨ht1, ht2⟩ := mem_pow.mp ht
    obtain ⟨z, hz, hmem⟩ := (BT.ex (Γ := [0, 2]) 1
      ((singB.sub [0, 1] 0).and (BT.mem 0 2 1 rfl rfl))).set (fun _ => t)
    have hmem' : ∀ x, Mem x z ↔ Mem (sing x) t := fun x => (hmem x).trans
      ⟨fun ⟨u, (e : u = sing x), (h : Mem u t)⟩ => e ▸ h, fun h => ⟨_, rfl, h⟩⟩
    have hza : Sub z a := fun x hx => mem_simg_sing.mp (ht2 _ ((hmem' x).mp hx))
    refine ⟨sing z, z, ⟨hz, hza⟩, rfl, ?_⟩
    refine set_ext ht1 isSet_simg fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · obtain ⟨x, -, rfl⟩ := mem_simg.mp (ht2 w hw)
      exact mem_simg_sing.mpr ((hmem' x).mpr hw)
    · obtain ⟨x, hx, rfl⟩ := mem_simg.mp hw
      exact (hmem' x).mp hx
  · rintro t u u' ⟨z, hz, rfl, rfl⟩ ⟨z', hz', rfl, e⟩
    rw [simg_inj hz.1 hz'.1 e]
  · rintro t t' u ⟨z, _, rfl, rfl⟩ ⟨z', _, e, rfl⟩
    rw [sing_inj e]

theorem simg_pow_eqv (a : M) : Eqv (simg (pow a)) (pow (simg a)) :=
  ⟨simg_pow_le a, pow_simg_le a⟩

/-- A set that injects into a set of singletons is equinumerous with a set of singletons. -/
theorem le_simg_ex {a z : M} (h : Le a (simg z)) : ∃ y, Eqv a (simg y) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨y, -, hy⟩ := (BT.ex (Γ := [0, 4]) 1 (BT.ex 1
    ((apB.sub [3, 1, 0] 1).and (singB.sub [0, 2] 0)))).set (fun _ => f)
  have hy' : ∀ u, Mem u y ↔ ∃ x, Ap f x (sing u) := fun u => (hy u).trans
    ⟨fun ⟨x, t, (h : Ap f x t), (e : t = sing u)⟩ => ⟨x, e ▸ h⟩, fun ⟨x, h⟩ => ⟨x, _, h, rfl⟩⟩
  have hran : ∀ x t, Ap f x t → Mem t (simg y) := by
    intro x t h
    obtain ⟨u, -, rfl⟩ := mem_simg.mp (hf.dom _ _ h).2
    exact mem_simg_sing.mpr ((hy' u).mpr ⟨x, h⟩)
  have hf' : Inj f a (simg y) :=
    ⟨fun x t h => ⟨(hf.dom _ _ h).1, hran x t h⟩, hf.tot, hf.func, hf.inj⟩
  refine ⟨y, ⟨f, hf'⟩, le_conv hf' fun t ht => ?_⟩
  obtain ⟨u, hu, rfl⟩ := mem_simg.mp ht
  exact (hy' u).mp hu

/-- **Cantor's theorem**: there is no injection of the power set of `y` into the set of
singletons of members of `y`. -/
theorem cantor (y : M) : ¬Le (pow y) (simg y) := by
  rintro ⟨g, hg⟩
  obtain ⟨D, hD, hmem⟩ := ((BT.mem (Γ := [0, 1, 4]) 0 1 0 rfl rfl).and
    (BT.ex 1 ((BT.ex 1 ((singB.sub [0, 2] 0).and (apB.sub [4, 1, 0] 1))).and
      ((BT.mem 1 0 0 rfl rfl).not)))).set (scons y (fun _ => g))
  have hmem' : ∀ x, Mem x D ↔ Mem x y ∧ ∃ z, Ap g z (sing x) ∧ ¬Mem x z := fun x =>
    (hmem x).trans (and_congr Iff.rfl
      ⟨fun ⟨z, ⟨u, (e : u = sing x), (h : Ap g z u)⟩, (hn : ¬Mem x z)⟩ => ⟨z, e ▸ h, hn⟩,
        fun ⟨z, h, hn⟩ => ⟨z, ⟨_, rfl, h⟩, hn⟩⟩)
  have hDy : Mem D (pow y) := mem_pow.mpr ⟨hD, fun x hx => ((hmem' x).mp hx).1⟩
  obtain ⟨t, ht⟩ := hg.tot D hDy
  obtain ⟨x₀, hx₀, rfl⟩ := mem_simg.mp (hg.dom _ _ ht).2
  by_cases h : Mem x₀ D
  · obtain ⟨-, z, hz, hnz⟩ := (hmem' x₀).mp h
    rw [hg.inj _ _ _ hz ht] at hnz
    exact hnz h
  · exact h ((hmem' x₀).mpr ⟨hx₀, D, ht, h⟩)

end

end FFL.FirstOrder.FNF
