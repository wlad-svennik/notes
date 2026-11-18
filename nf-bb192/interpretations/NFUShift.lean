import NFUInterpretsNFEq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# NFU without a designated empty set

In a model of NFU + Infinity a second membership relation is defined from membership alone,
without the predicate "is a set" and without parameters. For it, the set of all singletons
(the number one) has no members, the successor of a positive number `k` has the members of `k`,
and every other object keeps its members. With "is a set" read as "has a member in the old
sense", the new structure satisfies the axioms of NFU with a predicate for sethood, and
Infinity.

This is what is needed to pass from Jensen's NFU, in the language of membership and equality,
to NFU with a predicate for sethood: in Jensen's NFU no object without members is definable, so
the empty set of the new structure has to be an object with members.
-/

namespace NFUCut

/-! ### Three facts about formulas -/

namespace Fml

/-- The name `i` occurs free in the formula. -/
def Free (i : ℕ) : Fml → Prop
  | mem x y => i = x ∨ i = y
  | eq x y => i = x ∨ i = y
  | set x => i = x
  | neg φ => Free i φ
  | and φ ψ => Free i φ ∨ Free i ψ
  | all x φ => i ≠ x ∧ Free i φ

/-- The formula has no atomic subformula "is a set". -/
def noSet : Fml → Bool
  | mem _ _ => true
  | eq _ _ => true
  | set _ => false
  | neg φ => noSet φ
  | and φ ψ => noSet φ && noSet ψ
  | all _ φ => noSet φ

/-- Raising every type by the same amount preserves stratification. -/
theorem strat_add {σ : ℕ → ℕ} (t : ℕ) (φ : Fml) (h : φ.strat σ = true) :
    φ.strat (fun i => σ i + t) = true := by
  induction φ with
  | mem x y => simp only [strat, beq_iff_eq] at h ⊢; omega
  | eq x y => simp only [strat, beq_iff_eq] at h ⊢; omega
  | set x => rfl
  | neg φ ih => exact ih h
  | and φ ψ ih1 ih2 =>
    simp only [strat, Bool.and_eq_true] at h ⊢
    exact ⟨ih1 h.1, ih2 h.2⟩
  | all x φ ih => exact ih h

end Fml

/-- A formula without "is a set" has the same meaning whatever the sets are. -/
theorem sat_congr_isSet {V : Type} (mem : V → V → Prop) (isSet isSet' : V → Prop) (φ : Fml)
    (h : φ.noSet = true) : ∀ ρ : ℕ → V, Sat mem isSet φ ρ ↔ Sat mem isSet' φ ρ := by
  induction φ with
  | mem x y => intro ρ; rfl
  | eq x y => intro ρ; rfl
  | set x => exact absurd h (by simp [Fml.noSet])
  | neg φ ih => intro ρ; simp only [Sat]; rw [ih h ρ]
  | and φ ψ ih1 ih2 =>
    intro ρ
    simp only [Fml.noSet, Bool.and_eq_true] at h
    simp only [Sat]
    rw [ih1 h.1 ρ, ih2 h.2 ρ]
  | all x φ ih =>
    intro ρ
    simp only [Sat]
    exact forall_congr' fun a => ih h _

namespace Model

variable {V : Type} [Nonempty V] (M : Model V)

/-! ### The definitions -/

/-- `s` has the members of the successor of `k`. -/
def SuccW (s k : V) : Prop :=
  ∀ y, M.mem y s ↔ ∃ x b, M.mem x k ∧ ¬ M.mem b x ∧ y = M.adj x b

/-- The members of `w` are the singletons. -/
def OneW (w : V) : Prop := ∀ y, M.mem y w ↔ ∃ a, y = M.sing a

/-- `u` is a positive number: it belongs to every family that contains the number one and is
closed under successor. -/
def InP (u : V) : Prop :=
  ∀ I, ((∀ w, M.OneW w → M.mem w I) ∧ (∀ m, M.mem m I → ∀ m', M.SuccW m' m → M.mem m' I)) →
    M.mem u I

/-- **The new membership relation.** -/
def MemS (x y : V) : Prop :=
  (∃ k, M.InP k ∧ M.SuccW y k ∧ M.mem x k) ∨ (¬ M.InP y ∧ M.mem x y)

/-! ### The same as formulas, without "is a set" -/

def fSuccW (s k y x b z : ℕ) : Fml := .all y (Fml.iff (.mem y s) (fSuccMem y k x b z))

def fOneW (w y a z : ℕ) : Fml := .all y (Fml.iff (.mem y w) (Fml.ex a (fSing y a z)))

def fInP (u : ℕ) : Fml :=
  .all 3 (Fml.imp
    (.and (.all 4 (Fml.imp (fOneW 4 7 8 9) (.mem 4 3)))
      (.all 5 (Fml.imp (.mem 5 3) (.all 6 (Fml.imp (fSuccW 6 5 7 10 8 9) (.mem 6 3))))))
    (.mem u 3))

/-- The new membership relation, between the names `0` and `1`. -/
def fMemS : Fml :=
  Fml.or (Fml.ex 2 (.and (fInP 2) (.and (fSuccW 1 2 7 10 8 9) (.mem 0 2))))
    (.and (.neg (fInP 1)) (.mem 0 1))

/-- A stratification of `fMemS`: the name `0` has type 1 and the name `1` has type 2. -/
def σMemS : ℕ → ℕ := fun i =>
  if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 2 else if i = 3 then 3
  else if i = 4 then 2 else if i = 5 then 2 else if i = 6 then 2 else if i = 7 then 1
  else if i = 10 then 1 else 0

theorem fMemS_strat : fMemS.strat σMemS = true := by decide

theorem fMemS_noSet : fMemS.noSet = true := by decide

theorem fMemS_free {i : ℕ} (h : fMemS.Free i) : i = 0 ∨ i = 1 := by
  simp only [fMemS, fInP, fSuccW, fOneW, fSuccMem, fSing, fAdj, Fml.or, Fml.ex, Fml.imp,
    Fml.iff, Fml.Free] at h
  omega

theorem sat_fSuccW {s k y x b z : ℕ} (hsy : s ≠ y) (hky : k ≠ y) (hyx : y ≠ x) (hyb : y ≠ b)
    (hyz : y ≠ z) (hkx : k ≠ x) (hkb : k ≠ b) (hxb : x ≠ b) (hxz : x ≠ z) (hbz : b ≠ z)
    (ρ : ℕ → V) : Sat M.mem M.isSet (fSuccW s k y x b z) ρ ↔ M.SuccW (ρ s) (ρ k) := by
  simp only [fSuccW, SuccW, Sat, M.sat_iff, M.sat_fSuccMem hyx hyb hyz hkx hkb hxb hxz hbz,
    Function.update_self, Function.update_of_ne hsy, Function.update_of_ne hky]

theorem sat_fOneW {w y a z : ℕ} (hwy : w ≠ y) (hya : y ≠ a) (hyz : y ≠ z) (haz : a ≠ z)
    (ρ : ℕ → V) : Sat M.mem M.isSet (fOneW w y a z) ρ ↔ M.OneW (ρ w) := by
  simp only [fOneW, OneW, Sat, M.sat_iff, M.sat_ex, M.sat_fSing hyz haz, Function.update_self,
    Function.update_of_ne hwy, Function.update_of_ne hya]

theorem sat_fInP {u : ℕ} (hu : u < 3 ∨ 10 < u) (ρ : ℕ → V) :
    Sat M.mem M.isSet (fInP u) ρ ↔ M.InP (ρ u) := by
  have h3 : u ≠ 3 := by omega
  simp only [fInP, InP, Sat, M.sat_imp,
    M.sat_fOneW (w := 4) (y := 7) (a := 8) (z := 9) (by decide) (by decide) (by decide)
      (by decide),
    M.sat_fSuccW (s := 6) (k := 5) (y := 7) (x := 10) (b := 8) (z := 9) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff, h3]

theorem sat_fMemS (ρ : ℕ → V) : Sat M.mem M.isSet fMemS ρ ↔ M.MemS (ρ 0) (ρ 1) := by
  simp only [fMemS, MemS, Sat, M.sat_or, M.sat_ex, M.sat_fInP (u := 2) (by decide),
    M.sat_fInP (u := 1) (by decide),
    M.sat_fSuccW (s := 1) (k := 2) (y := 7) (x := 10) (b := 8) (z := 9) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  simp only [Function.update_apply]
  simp only [reduceIte, Nat.reduceEqDiff]

/-! ### The number one -/

theorem mem_one {y : V} : M.mem y (M.succ M.zero) ↔ ∃ a, y = M.sing a := by
  rw [M.mem_succ]
  constructor
  · rintro ⟨x, b, hx, -, rfl⟩
    have e : x = M.emp := M.mem_zero.mp hx
    refine ⟨b, M.eq_sing_iff.mp fun c => ?_⟩
    rw [M.mem_adj, e]
    exact ⟨fun h => h.elim (fun h => absurd h (M.not_mem_emp c)) id, Or.inr⟩
  · rintro ⟨a, rfl⟩
    refine ⟨M.emp, a, M.mem_zero.mpr rfl, M.not_mem_emp a, M.eq_adj_iff.mp fun c => ?_⟩
    rw [M.mem_sing]
    exact ⟨Or.inr, fun h => h.elim (fun h => absurd h (M.not_mem_emp c)) id⟩

theorem oneW_iff {w : V} : M.OneW w ↔ w = M.succ M.zero := by
  constructor
  · intro h
    have hw : M.isSet w := M.isSet_of_mem ((h (M.sing dflt)).mpr ⟨dflt, rfl⟩)
    exact M.ext hw (M.succ_isSet _) fun y => (h y).trans M.mem_one.symm
  · rintro rfl y
    exact M.mem_one

/-! ### With Infinity -/

variable [hinf : Fact M.Infinity]

theorem succW_iff {s k : V} (hk : M.mem k M.nat) : M.SuccW s k ↔ s = M.succ k := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := M.nat_nonempty (M.succ_mem_nat hk)
    have hs : M.isSet s := M.isSet_of_mem ((h v).mpr (M.mem_succ.mp hv))
    exact M.ext hs (M.succ_isSet k) fun y => (h y).trans M.mem_succ.symm
  · rintro rfl y
    exact M.mem_succ

/-- The types used for the two sets of numbers in `inP_iff`. -/
private def σPos : ℕ → ℕ := fun i =>
  if i = 2 then 3 else if i = 0 then 2 else if i = 1 then 2 else if i = 5 then 1
  else if i = 6 then 1 else 0

/-- The positive numbers are the successors of the natural numbers. -/
theorem inP_iff {u : V} : M.InP u ↔ ∃ n, M.mem n M.nat ∧ u = M.succ n := by
  constructor
  · intro h
    obtain ⟨I, -, hI⟩ := M.comp σPos (Fml.ex 1 (.and (.mem 1 2) (fSucc 0 1 5 6 7 8))) 0
      (by decide) (Function.update (fun _ => dflt) 2 M.nat)
    have hI' : ∀ u, M.mem u I ↔ ∃ n, M.mem n M.nat ∧ u = M.succ n := by
      intro u
      rw [hI u]
      simp only [M.sat_ex, Sat,
        M.sat_fSucc (s := 0) (k := 1) (y := 5) (x := 6) (b := 7) (z := 8) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
      simp only [Function.update_apply]
      simp only [reduceIte, Nat.reduceEqDiff]
    refine (hI' u).mp (h I ⟨fun w hw => ?_, fun m hm m' hm' => ?_⟩)
    · exact (hI' w).mpr ⟨M.zero, M.zero_mem_nat, M.oneW_iff.mp hw⟩
    · obtain ⟨n, hn, rfl⟩ := (hI' m).mp hm
      exact (hI' m').mpr
        ⟨M.succ n, M.succ_mem_nat hn, (M.succW_iff (M.succ_mem_nat hn)).mp hm'⟩
  · rintro ⟨n, hn, rfl⟩ I ⟨h1, h2⟩
    obtain ⟨J, -, hJ⟩ := M.comp σPos (Fml.ex 1 (.and (.mem 1 2) (fSucc 1 0 5 6 7 8))) 0
      (by decide) (Function.update (fun _ => dflt) 2 I)
    have hJ' : ∀ k, M.mem k J ↔ M.mem (M.succ k) I := by
      intro k
      rw [hJ k]
      simp only [M.sat_ex, Sat,
        M.sat_fSucc (s := 1) (k := 0) (y := 5) (x := 6) (b := 7) (z := 8) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
      simp only [Function.update_apply]
      simp only [reduceIte, Nat.reduceEqDiff]
      exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨_, h, rfl⟩⟩
    exact (hJ' n).mp (M.nat_ind ((hJ' _).mpr (h1 _ (M.oneW_iff.mpr rfl)))
      (fun k hk => (hJ' _).mpr (h2 _ ((hJ' k).mp hk) _ (fun y => M.mem_succ))) hn)

theorem memS_iff {x y : V} : M.MemS x y ↔
    (∃ n, M.mem n M.nat ∧ y = M.succ (M.succ n) ∧ M.mem x (M.succ n)) ∨
      ((¬ ∃ n, M.mem n M.nat ∧ y = M.succ n) ∧ M.mem x y) := by
  unfold MemS
  constructor
  · rintro (⟨k, hk, hyk, hxk⟩ | ⟨hy, hxy⟩)
    · obtain ⟨n, hn, rfl⟩ := M.inP_iff.mp hk
      exact Or.inl ⟨n, hn, (M.succW_iff (M.succ_mem_nat hn)).mp hyk, hxk⟩
    · exact Or.inr ⟨fun h => hy (M.inP_iff.mpr h), hxy⟩
  · rintro (⟨n, hn, rfl, hx⟩ | ⟨hy, hxy⟩)
    · exact Or.inl ⟨M.succ n, M.inP_iff.mpr ⟨n, hn, rfl⟩,
        (M.succW_iff (M.succ_mem_nat hn)).mpr rfl, hx⟩
    · exact Or.inr ⟨fun h => hy (M.inP_iff.mp h), hxy⟩

theorem one_ne_succ_succ {n : V} (hn : M.mem n M.nat) :
    M.succ M.zero ≠ M.succ (M.succ n) := fun h =>
  M.zero_ne_succ n (M.succ_inj M.zero_mem_nat (M.succ_mem_nat hn) h)

/-- The number one has no members in the new sense: it is the new empty set. -/
theorem not_memS_one (x : V) : ¬ M.MemS x (M.succ M.zero) := by
  rw [M.memS_iff]
  rintro (⟨n, hn, h, -⟩ | ⟨h, -⟩)
  · exact M.one_ne_succ_succ hn h
  · exact h ⟨M.zero, M.zero_mem_nat, rfl⟩

/-- The successor of a positive number `k` has the members of `k`. -/
theorem memS_succ_succ {n : V} (hn : M.mem n M.nat) {x : V} :
    M.MemS x (M.succ (M.succ n)) ↔ M.mem x (M.succ n) := by
  rw [M.memS_iff]
  constructor
  · rintro (⟨n', hn', h, hx⟩ | ⟨h, -⟩)
    · have e : M.succ n = M.succ n' :=
        M.succ_inj (M.succ_mem_nat hn) (M.succ_mem_nat hn') h
      rw [e]
      exact hx
    · exact absurd ⟨M.succ n, M.succ_mem_nat hn, rfl⟩ h
  · intro hx
    exact Or.inl ⟨n, hn, rfl, hx⟩

/-- An object that is not a positive number keeps its members. -/
theorem memS_of_not {y : V} (hP : ¬ ∃ n, M.mem n M.nat ∧ y = M.succ n) {x : V} :
    M.MemS x y ↔ M.mem x y := by
  rw [M.memS_iff]
  constructor
  · rintro (⟨n', hn', h, -⟩ | ⟨-, hx⟩)
    · exact absurd ⟨M.succ n', M.succ_mem_nat hn', h⟩ hP
    · exact hx
  · intro hx
    exact Or.inr ⟨hP, hx⟩

/-- Only objects with members in the old sense have members in the new sense. -/
theorem memS_nonempty {x y : V} (h : M.MemS x y) : ∃ v, M.mem v y := by
  rcases M.memS_iff.mp h with ⟨n, hn, rfl, -⟩ | ⟨-, hxy⟩
  · exact M.nat_nonempty (M.succ_mem_nat (M.succ_mem_nat hn))
  · exact ⟨x, hxy⟩

/-- **Every collection has a code**: for every object `z` there is an object with members whose
members in the new sense are the members of `z`. -/
theorem exists_codeS (z : V) : ∃ y, (∃ v, M.mem v y) ∧ ∀ x, M.MemS x y ↔ M.mem x z := by
  by_cases hz : ∃ v, M.mem v z
  · by_cases hP : ∃ n, M.mem n M.nat ∧ z = M.succ n
    · obtain ⟨n, hn, rfl⟩ := hP
      exact ⟨M.succ (M.succ n), M.nat_nonempty (M.succ_mem_nat (M.succ_mem_nat hn)),
        fun x => M.memS_succ_succ hn⟩
    · exact ⟨z, hz, fun x => M.memS_of_not hP⟩
  · refine ⟨M.succ M.zero, M.nat_nonempty (M.succ_mem_nat M.zero_mem_nat), fun x => ?_⟩
    exact ⟨fun h => absurd h (M.not_memS_one x), fun h => absurd ⟨x, h⟩ hz⟩

/-- The three kinds of objects with members. -/
theorem memS_cases {y : V} (hy : ∃ v, M.mem v y) :
    y = M.succ M.zero ∨ (∃ k, M.mem k M.nat ∧ y = M.succ (M.succ k)) ∨
      ¬ ∃ n, M.mem n M.nat ∧ y = M.succ n := by
  by_cases hP : ∃ n, M.mem n M.nat ∧ y = M.succ n
  · obtain ⟨n, hn, rfl⟩ := hP
    rcases M.nat_cases hn with rfl | ⟨k, hk, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨k, hk, rfl⟩)
  · exact Or.inr (Or.inr hP)

/-- **Extensionality for the new membership relation**, for objects with members in the old
sense. -/
theorem memS_ext {y y' : V} (hy : ∃ v, M.mem v y) (hy' : ∃ v, M.mem v y')
    (h : ∀ x, M.MemS x y ↔ M.MemS x y') : y = y' := by
  have hset : ∀ {a : V}, (∃ v, M.mem v a) → M.isSet a := fun ⟨v, hv⟩ => M.isSet_of_mem hv
  rcases M.memS_cases hy with rfl | ⟨k, hk, rfl⟩ | hC
  · rcases M.memS_cases hy' with rfl | ⟨k', hk', rfl⟩ | hC'
    · rfl
    · obtain ⟨v, hv⟩ := M.nat_nonempty (M.succ_mem_nat hk')
      exact absurd ((h v).mpr ((M.memS_succ_succ hk').mpr hv)) (M.not_memS_one v)
    · obtain ⟨v, hv⟩ := hy'
      exact absurd ((h v).mpr ((M.memS_of_not hC').mpr hv)) (M.not_memS_one v)
  · rcases M.memS_cases hy' with rfl | ⟨k', hk', rfl⟩ | hC'
    · obtain ⟨v, hv⟩ := M.nat_nonempty (M.succ_mem_nat hk)
      exact absurd ((h v).mp ((M.memS_succ_succ hk).mpr hv)) (M.not_memS_one v)
    · have e : M.succ k = M.succ k' := M.ext (M.succ_isSet k) (M.succ_isSet k') fun x =>
        (M.memS_succ_succ hk).symm.trans ((h x).trans (M.memS_succ_succ hk'))
      rw [e]
    · have e : y' = M.succ k := M.ext (hset hy') (M.succ_isSet k) fun x =>
        (M.memS_of_not hC').symm.trans ((h x).symm.trans (M.memS_succ_succ hk))
      exact absurd ⟨k, hk, e⟩ hC'
  · rcases M.memS_cases hy' with rfl | ⟨k', hk', rfl⟩ | hC'
    · obtain ⟨v, hv⟩ := hy
      exact absurd ((h v).mp ((M.memS_of_not hC).mpr hv)) (M.not_memS_one v)
    · have e : y = M.succ k' := M.ext (hset hy) (M.succ_isSet k') fun x =>
        (M.memS_of_not hC).symm.trans ((h x).trans (M.memS_succ_succ hk'))
      exact absurd ⟨k', hk', e⟩ hC
    · exact M.ext (hset hy) (hset hy') fun x =>
        (M.memS_of_not hC).symm.trans ((h x).trans (M.memS_of_not hC'))

/-- The types used for the family of finite sets in `shift_infinity`. -/
private def σFinS : ℕ → ℕ := fun i =>
  if i = 11 then 2 else if i = 12 then 4 else if i = 13 then 1 else if i = 28 then 3 else σMemS i

/-- **Infinity for the new membership relation.** Some family contains every empty set, is
closed under adjoining one element, and contains no universal set, all in the new sense. -/
theorem shift_infinity :
    ∃ F, (∀ e, (∃ v, M.mem v e) → (∀ z, ¬ M.MemS z e) → M.MemS e F) ∧
      (∀ a, M.MemS a F → ∀ b a', (∃ v, M.mem v a') →
        (∀ z, M.MemS z a' ↔ M.MemS z a ∨ z = b) → M.MemS a' F) ∧
      ∀ u, (∀ z, M.MemS z u) → ¬ M.MemS u F := by
  obtain ⟨G, -, hG⟩ := M.comp σFinS
    (.and (Fml.ex 13 (.mem 13 1))
      (Fml.ex 11 (.and (fFin 11 12) (.all 0 (Fml.iff fMemS (.mem 0 11))))))
    1 (by decide) (Function.update (fun _ => dflt) 12 M.nat)
  have hG' : ∀ a, M.mem a G ↔
      (∃ v, M.mem v a) ∧ ∃ z, M.Fin z ∧ ∀ x, (M.MemS x a ↔ M.mem x z) := by
    intro a
    rw [hG a]
    simp only [M.sat_ex, Sat, M.sat_iff, M.sat_fFin (x := 11) (N := 12) (by decide) (by decide),
      M.sat_fMemS]
    simp only [Function.update_apply]
    simp only [reduceIte, Nat.reduceEqDiff]
    rfl
  obtain ⟨F, -, hF⟩ := M.exists_codeS G
  refine ⟨F, fun e he hno => ?_, fun a ha b a' ha' hz => ?_, fun u hu huF => ?_⟩
  · exact (hF e).mpr ((hG' e).mpr ⟨he, M.emp, M.fin_emp, fun x =>
      ⟨fun h => absurd h (hno x), fun h => absurd h (M.not_mem_emp x)⟩⟩)
  · obtain ⟨-, z, hz1, hz2⟩ := (hG' a).mp ((hF a).mp ha)
    exact (hF a').mpr ((hG' a').mpr ⟨ha', M.adj z b, M.fin_adj b hz1, fun x => by
      rw [hz x, hz2 x, M.mem_adj]⟩)
  · obtain ⟨-, z, hz1, hz2⟩ := (hG' u).mp ((hF u).mp huF)
    have e : z = M.univ := M.ext hz1.1 M.univ_isSet fun x =>
      ⟨fun _ => M.mem_univ x, fun _ => (hz2 x).mp (hu x)⟩
    obtain ⟨-, k, hk, hzk⟩ := hz1
    rw [e] at hzk
    exact hinf.out k hk hzk

end Model

end NFUCut
