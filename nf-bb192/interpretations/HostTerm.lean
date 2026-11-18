import Host
set_option autoImplicit false

/-! ## Phase 2 (A1): a copy of the numbers of a host; increasing sequences; halving -/

/-- A correspondence between a structure of numbers `N` and the numbers of a host. -/
structure NumIso {N : Type} [Zero N] [One N] [Add N] [LE N] (H : Host) (num : N → H.W) : Prop where
  zero : num 0 = H.emp
  succ : ∀ i, num (i + 1) = H.suc (num i)
  inj : ∀ i i', num i = num i' → i = i'
  onto : ∀ z, z ∈ H.om ↔ ∃ i, z = num i
  mem : ∀ i k, num i ∈ num k ↔ i + 1 ≤ k

/-- Facts about a structure of numbers that are used on the host side. `E` is `x ↦ 2^x`. -/
structure NFacts (N : Type) [CommSemiring N] [PartialOrder N] (E : N → N) : Prop where
  le_iff : ∀ a b : N, a ≤ b ↔ ∃ c, a + c = b
  total : ∀ a b : N, a ≤ b ∨ b ≤ a
  cancel : ∀ a b c : N, a + c = b + c → a = b
  not_succ_le : ∀ a : N, ¬ a + 1 ≤ a
  eq_or_succ_le : ∀ a b : N, a ≤ b → a = b ∨ a + 1 ≤ b
  zero_or_succ : ∀ a : N, a = 0 ∨ ∃ b, a = b + 1
  E_zero : E 0 = 1
  E_add : ∀ a b, E (a + b) = E a * E b
  E_one : E 1 = 2
  E_pos : ∀ a, 1 ≤ E a
  le_mul_self : ∀ z : N, z ≤ z * z
  cast_inj : ∀ a b : ℕ, ((a : ℕ) : N) = ((b : ℕ) : N) → a = b
  pair_inj : ∀ x y x' y' : N, (x + y) * (x + y) + x = (x' + y') * (x' + y') + x' → x = x' ∧ y = y'

namespace NFacts

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} (nf : NFacts N E)
include nf

theorem le_add (a c : N) : a ≤ a + c := (nf.le_iff _ _).mpr ⟨c, rfl⟩

theorem zero_le (a : N) : 0 ≤ a := (nf.le_iff _ _).mpr ⟨a, zero_add a⟩

theorem add_le_add_r {a b : N} (h : a ≤ b) (c : N) : a + c ≤ b + c := by
  obtain ⟨d, hd⟩ := (nf.le_iff a b).mp h
  exact (nf.le_iff _ _).mpr ⟨d, by rw [← hd]; ring⟩

theorem add_le_add_l {a b : N} (h : a ≤ b) (c : N) : c + a ≤ c + b := by
  rw [add_comm c a, add_comm c b]
  exact nf.add_le_add_r h c

theorem mul_le_mul_l {a b : N} (h : a ≤ b) (c : N) : c * a ≤ c * b := by
  obtain ⟨d, hd⟩ := (nf.le_iff a b).mp h
  exact (nf.le_iff _ _).mpr ⟨c * d, by rw [← hd]; ring⟩

theorem le_of_add_le_add_r {a b c : N} (h : a + c ≤ b + c) : a ≤ b := by
  obtain ⟨d, hd⟩ := (nf.le_iff _ _).mp h
  refine (nf.le_iff _ _).mpr ⟨d, nf.cancel _ _ c ?_⟩
  rw [← hd]
  ring

theorem le_of_add_le_add_l {a b c : N} (h : c + a ≤ c + b) : a ≤ b := by
  rw [add_comm c a, add_comm c b] at h
  exact nf.le_of_add_le_add_r h

theorem succ_inj {a b : N} (h : a + 1 = b + 1) : a = b := nf.cancel a b 1 h

theorem le_of_succ_le_succ {a b : N} (h : a + 1 ≤ b + 1) : a ≤ b := nf.le_of_add_le_add_r h

theorem le_or_succ_le (a b : N) : a ≤ b ∨ b + 1 ≤ a := by
  rcases nf.total a b with h | h
  · exact Or.inl h
  · rcases nf.eq_or_succ_le b a h with e | e
    · exact Or.inl (le_of_eq e.symm)
    · exact Or.inr e

theorem E_succ (a : N) : E (a + 1) = E a + E a := by
  rw [nf.E_add, nf.E_one, mul_two]

theorem E_mono {a b : N} (h : a ≤ b) : E a ≤ E b := by
  obtain ⟨d, rfl⟩ := (nf.le_iff a b).mp h
  rw [nf.E_add]
  have := nf.mul_le_mul_l (nf.E_pos d) (E a)
  rwa [mul_one] at this

theorem half {a b n : N} (h : n + n ≤ a + b) : n ≤ a ∨ n ≤ b := by
  rcases nf.total n a with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (nf.le_of_add_le_add_l (le_trans h (nf.add_le_add_r h1 b)))

end NFacts

namespace Host

/-- The numbers of the host are a copy of `N` under `num`, and the graphs of addition, of
multiplication and of `E` on the numbers of the host are definable. -/
structure Arith (H : Host) {N : Type} [CommSemiring N] [PartialOrder N] (E : N → N)
    (num : N → H.W) : Prop where
  iso : NumIso H num
  nf : NFacts N E
  add : ∃ A : H.W → H.W → H.W → Prop, Def3 H A ∧ ∀ a b z, A (num a) (num b) z ↔ z = num (a + b)
  mul : ∃ A : H.W → H.W → H.W → Prop, Def3 H A ∧ ∀ a b z, A (num a) (num b) z ↔ z = num (a * b)
  exp : ∃ A : H.W → H.W → Prop, Def2 H A ∧ ∀ a z, A (num a) z ↔ z = num (E a)

variable {H : Host}

namespace Arith

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}
variable (ar : H.Arith E num)
include ar

theorem num_om (i : N) : num i ∈ H.om := (ar.iso.onto _).mpr ⟨i, rfl⟩

theorem of_om {x : H.W} (h : x ∈ H.om) : ∃ i, x = num i := (ar.iso.onto x).mp h

theorem num_inj {i k : N} (h : num i = num k) : i = k := ar.iso.inj i k h

theorem num_mem {i k : N} : num i ∈ num k ↔ i + 1 ≤ k := ar.iso.mem i k

theorem mem_num {z : H.W} {k : N} : z ∈ num k ↔ ∃ i, i + 1 ≤ k ∧ z = num i := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := ar.of_om (H.mem_om_of_mem (ar.num_om k) h)
    exact ⟨i, ar.num_mem.mp h, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ar.num_mem.mpr hi

theorem num_le {a b : N} : (num a ∈ num b ∨ num a = num b) ↔ a ≤ b := by
  constructor
  · rintro (h | h)
    · exact le_trans (ar.nf.le_add a 1) (ar.num_mem.mp h)
    · exact le_of_eq (ar.num_inj h)
  · intro h
    rcases ar.nf.eq_or_succ_le a b h with e | e
    · exact Or.inr (by rw [e])
    · exact Or.inl (ar.num_mem.mpr e)

/-- The graph of addition on the numbers of the host. -/
noncomputable def Ad : H.W → H.W → H.W → Prop := Classical.choose ar.add

theorem def_Ad : Def3 H ar.Ad := (Classical.choose_spec ar.add).1

theorem ad_iff {a b : N} {z : H.W} : ar.Ad (num a) (num b) z ↔ z = num (a + b) :=
  (Classical.choose_spec ar.add).2 a b z

/-- The graph of multiplication on the numbers of the host. -/
noncomputable def Mu : H.W → H.W → H.W → Prop := Classical.choose ar.mul

theorem def_Mu : Def3 H ar.Mu := (Classical.choose_spec ar.mul).1

theorem mu_iff {a b : N} {z : H.W} : ar.Mu (num a) (num b) z ↔ z = num (a * b) :=
  (Classical.choose_spec ar.mul).2 a b z

/-- The graph of `E` on the numbers of the host. -/
noncomputable def Ex : H.W → H.W → Prop := Classical.choose ar.exp

theorem def_Ex : Def2 H ar.Ex := (Classical.choose_spec ar.exp).1

theorem ex_iff {a : N} {z : H.W} : ar.Ex (num a) z ↔ z = num (E a) :=
  (Classical.choose_spec ar.exp).2 a z

theorem num_sub {i k : N} (h : i ≤ k) : H.Sub (num i) (num k) := by
  intro z hz
  obtain ⟨j, hj, rfl⟩ := ar.mem_num.mp hz
  exact ar.num_mem.mpr (le_trans hj h)

/-- Induction over `N` for a definable predicate of the corresponding numbers of the host. -/
theorem num_ind (P : H.W → Prop) (hP : Def1 H P) (h0 : P (num 0))
    (hs : ∀ i, P (num i) → P (num (i + 1))) : ∀ i, P (num i) := by
  have key := H.om_ind P hP (by rw [← ar.iso.zero]; exact h0) (fun n hn hPn => by
    obtain ⟨i, rfl⟩ := ar.of_om hn
    rw [← ar.iso.succ]
    exact hs i hPn)
  exact fun i => key _ (ar.num_om i)

end Arith

/-! ### Increasing sequences of numbers -/

/-- `f` is an increasing sequence of numbers of length `n`. -/
def IncSeq (f n : H.W) : Prop :=
  H.FunOn f n ∧ n ∈ H.om ∧ (∀ i a, H.App f i a → a ∈ H.om) ∧
    ∀ i j a b, H.App f i a → H.App f j b → i ∈ j → a ∈ b

theorem def_incSeq : Def2 H (fun f n => H.IncSeq f n) := by hdef

/-- Every value of `g` is a value of `f`. -/
def SubSeq (g f : H.W) : Prop := ∀ i a, H.App g i a → ∃ j, H.App f j a

theorem SubSeq.trans {f g h : H.W} (h1 : H.SubSeq h g) (h2 : H.SubSeq g f) : H.SubSeq h f :=
  fun i a hi => by
    obtain ⟨j, hj⟩ := h1 i a hi
    exact h2 j a hj

theorem incSeq_emp : H.IncSeq H.emp H.emp :=
  ⟨H.funOn_emp, H.emp_mem_om, fun i a h => (H.not_mem_emp _ (H.app_iff.mp h)).elim,
    fun i j a b h => (H.not_mem_emp _ (H.app_iff.mp h)).elim⟩

namespace IncSeq

variable {f n : H.W} (hf : H.IncSeq f n)
include hf

theorem tot {i : H.W} (hi : i ∈ n) : ∃ a, H.App f i a := (hf.1.2 i).mp hi

theorem dom {i a : H.W} (h : H.App f i a) : i ∈ n := (hf.1.2 i).mpr ⟨a, h⟩

theorem fn {i a b : H.W} (h : H.App f i a) (h' : H.App f i b) : a = b := hf.1.1.2 i a b h h'

theorem res {m : H.W} (hm : m ∈ H.om) (hsub : H.Sub m n) : H.IncSeq (H.res f m) m :=
  ⟨H.funOn_res hf.1 hsub, hm, fun i a h => hf.2.2.1 i a (H.app_res.mp h).2,
    fun i j a b h h' hij => hf.2.2.2 i j a b (H.app_res.mp h).2 (H.app_res.mp h').2 hij⟩

theorem res_sub (m : H.W) : H.SubSeq (H.res f m) f := fun i a h => ⟨i, (H.app_res.mp h).2⟩

theorem snoc {a : H.W} (ha : a ∈ H.om) (hab : ∀ i b, H.App f i b → b ∈ a) :
    H.IncSeq (H.ins f n a) (H.suc n) := by
  refine ⟨H.funOn_ins hf.1, H.suc_mem_om hf.2.1, fun i b h => ?_, fun i j b c h h' hij => ?_⟩
  · rcases H.app_ins.mp h with h1 | ⟨-, h1⟩
    · exact hf.2.2.1 i b h1
    · rw [h1]
      exact ha
  · rcases H.app_ins.mp h with h1 | ⟨e1, e2⟩
    · rcases H.app_ins.mp h' with h2 | ⟨e3, e4⟩
      · exact hf.2.2.2 i j b c h1 h2 hij
      · rw [e4]
        exact hab i b h1
    · rcases H.app_ins.mp h' with h2 | ⟨e3, e4⟩
      · rw [e1] at hij
        exact (H.mem_asymm hij (hf.dom h2)).elim
      · rw [e1, e3] at hij
        exact (H.mem_irrefl _ hij).elim

end IncSeq

/-! ### Halving -/

section halve

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- **Halving.** From an increasing sequence of length at least `2n` one can select an
increasing sequence of length `n` all of whose values have a given definable property, or
none of whose values has it. -/
theorem halve (ar : H.Arith E num) {G : H.W} {l n : N} (hG : H.IncSeq G (num l))
    (c : H.W → Prop) (hc : Def1 H c) (hn : n + n ≤ l) :
    ∃ G', H.IncSeq G' (num n) ∧ H.SubSeq G' G ∧
      ((∀ i a, H.App G' i a → c a) ∨ (∀ i a, H.App G' i a → ¬ c a)) := by
  obtain ⟨A, hA, hAs⟩ := ar.add
  have hdi := H.def_incSeq
  have key := ar.num_ind (fun x => (x ∈ num l ∨ x = num l) → ∃ G1 G0 a b, H.IncSeq G1 a ∧
      H.IncSeq G0 b ∧ A a b x ∧ (∀ i y, H.App G1 i y → c y ∧ ∃ j, j ∈ x ∧ H.App G j y) ∧
      (∀ i y, H.App G0 i y → ¬ c y ∧ ∃ j, j ∈ x ∧ H.App G j y)) (by hdef)
    (fun _ => ⟨H.emp, H.emp, num 0, num 0, by rw [ar.iso.zero]; exact H.incSeq_emp,
      by rw [ar.iso.zero]; exact H.incSeq_emp, (hAs 0 0 _).mpr (by rw [add_zero]),
      fun i y h => (H.not_mem_emp _ (H.app_iff.mp h)).elim,
      fun i y h => (H.not_mem_emp _ (H.app_iff.mp h)).elim⟩)
    (fun m ih hm => by
      have hml : num m ∈ num l := by
        rcases hm with h | h
        · exact H.om_mem_trans (ar.num_om l) h (ar.num_mem.mpr (le_refl _))
        · rw [← h]
          exact ar.num_mem.mpr (le_refl _)
      obtain ⟨G1, G0, a, b, h1, h0, hab, hc1, hc0⟩ := ih (Or.inl hml)
      obtain ⟨a0, rfl⟩ := ar.of_om h1.2.1
      obtain ⟨b0, rfl⟩ := ar.of_om h0.2.1
      have em : m = a0 + b0 := ar.num_inj ((hAs a0 b0 _).mp hab)
      obtain ⟨y, hy⟩ := hG.tot hml
      have hyo := hG.2.2.1 _ _ hy
      have hlow : ∀ {K : H.W}, (∀ i z, H.App K i z → ∃ j, j ∈ num m ∧ H.App G j z) →
          ∀ i z, H.App K i z → z ∈ y := fun hK i z hz => by
        obtain ⟨j, hj, hjz⟩ := hK i z hz
        exact hG.2.2.2 j (num m) z y hjz hy hj
      have hup : ∀ {z : H.W}, (∃ j, j ∈ num m ∧ H.App G j z) → ∃ j, j ∈ num (m + 1) ∧ H.App G j z :=
        fun ⟨j, hj, hjz⟩ => ⟨j, by rw [ar.iso.succ]; exact H.mem_suc.mpr (Or.inl hj), hjz⟩
      have hnew : ∃ j, j ∈ num (m + 1) ∧ H.App G j y :=
        ⟨num m, ar.num_mem.mpr (le_refl _), hy⟩
      by_cases hcy : c y
      · refine ⟨H.ins G1 (num a0) y, G0, num (a0 + 1), num b0, ?_, h0,
          (hAs _ _ _).mpr (by rw [em]; congr 1; ring), fun i z hz => ?_,
          fun i z hz => ⟨(hc0 i z hz).1, hup (hc0 i z hz).2⟩⟩
        · rw [ar.iso.succ]
          exact h1.snoc hyo (hlow fun i z hz => (hc1 i z hz).2)
        · rcases H.app_ins.mp hz with h | ⟨-, h⟩
          · exact ⟨(hc1 i z h).1, hup (hc1 i z h).2⟩
          · rw [h]
            exact ⟨hcy, hnew⟩
      · refine ⟨G1, H.ins G0 (num b0) y, num a0, num (b0 + 1), h1, ?_,
          (hAs _ _ _).mpr (by rw [em]; congr 1; ring),
          fun i z hz => ⟨(hc1 i z hz).1, hup (hc1 i z hz).2⟩, fun i z hz => ?_⟩
        · rw [ar.iso.succ]
          exact h0.snoc hyo (hlow fun i z hz => (hc0 i z hz).2)
        · rcases H.app_ins.mp hz with h | ⟨-, h⟩
          · exact ⟨(hc0 i z h).1, hup (hc0 i z h).2⟩
          · rw [h]
            exact ⟨hcy, hnew⟩)
  obtain ⟨G1, G0, a, b, h1, h0, hab, hc1, hc0⟩ := key l (Or.inr rfl)
  obtain ⟨a0, rfl⟩ := ar.of_om h1.2.1
  obtain ⟨b0, rfl⟩ := ar.of_om h0.2.1
  have el : l = a0 + b0 := ar.num_inj ((hAs a0 b0 _).mp hab)
  rw [el] at hn
  rcases ar.nf.half hn with h | h
  · exact ⟨H.res G1 (num n), h1.res (ar.num_om n) (ar.num_sub h),
      fun i z hz => by
        obtain ⟨j, -, hj⟩ := (hc1 i z (H.app_res.mp hz).2).2
        exact ⟨j, hj⟩,
      Or.inl fun i z hz => (hc1 i z (H.app_res.mp hz).2).1⟩
  · exact ⟨H.res G0 (num n), h0.res (ar.num_om n) (ar.num_sub h),
      fun i z hz => by
        obtain ⟨j, -, hj⟩ := (hc0 i z (H.app_res.mp hz).2).2
        exact ⟨j, hj⟩,
      Or.inr fun i z hz => (hc0 i z (H.app_res.mp hz).2).1⟩

end halve

end Host

/-! ## Phase 2 (A7, first part): refinement of a sequence for a family of tests -/

namespace Host

variable {H : Host}

/-- `B` is a set of values of `A` at arguments in `x`. -/
def SubR (B A x : H.W) : Prop := ∀ b, b ∈ B → ∃ j, j ∈ x ∧ H.App A j b

/-- The test "`T ∪ {x} ∈ c`" has the same outcome at all values `x` of `G`. -/
def Const (c T G : H.W) : Prop :=
  ∀ x y i j, H.App G i x → H.App G j y → (H.bun T (H.sg x) ∈ c ↔ H.bun T (H.sg y) ∈ c)

theorem Const.sub {c T G G' : H.W} (h : H.Const c T G) (hs : H.SubSeq G' G) : H.Const c T G' :=
  fun x y i j hx hy => by
    obtain ⟨i', hi'⟩ := hs i x hx
    obtain ⟨j', hj'⟩ := hs j y hy
    exact h x y i' j' hi' hj'

section refine

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- **Refinement.** Let `A` be a function and `c` a set. From an increasing sequence of length
at least `E(E(i)) · n` one can select an increasing sequence of length `n` on whose values all
the tests "`B ∪ P ∪ {x} ∈ c`", for `B` a set of values of `A` below `i`, are constant. -/
theorem refine_lemma (ar : H.Arith E num) (c A : H.W) (hA : H.IsFun A) :
    ∀ (i n l : N) (P G : H.W), E (E i) * n ≤ l → H.IncSeq G (num l) →
      ∃ G', H.IncSeq G' (num n) ∧ H.SubSeq G' G ∧
        ∀ B, H.SubR B A (num i) → H.Const c (H.bun B P) G' := by
  have hE := ar.def_Ex
  have hM := ar.def_Mu
  have hdi := H.def_incSeq
  have key := ar.num_ind (fun x => ∀ P n L G K e1 e2, ar.Ex x e1 → ar.Ex e1 e2 → ar.Mu e2 n K →
      (K ∈ L ∨ K = L) → n ∈ H.om → H.IncSeq G L →
      ∃ G', H.IncSeq G' n ∧ H.SubSeq G' G ∧ ∀ B, H.SubR B A x → H.Const c (H.bun B P) G')
    (by hdef) ?_ ?_
  · intro i n l P G hle hG
    exact key i P (num n) (num l) G (num (E (E i) * n)) (num (E i)) (num (E (E i)))
      (ar.ex_iff.mpr rfl) (ar.ex_iff.mpr rfl) (ar.mu_iff.mpr rfl) (ar.num_le.mpr hle)
      (ar.num_om n) hG
  · -- the base case: one test
    intro P n L G K e1 e2 h1 h2 h3 hK hn hG
    obtain ⟨n0, rfl⟩ := ar.of_om hn
    obtain ⟨l, rfl⟩ := ar.of_om hG.2.1
    rw [ar.ex_iff.mp h1] at h2
    rw [ar.ex_iff.mp h2] at h3
    rw [ar.mu_iff.mp h3] at hK
    have hle : n0 + n0 ≤ l := by
      have := ar.num_le.mp hK
      rwa [ar.nf.E_zero, ar.nf.E_one, two_mul] at this
    obtain ⟨G', hG', hsub, hc⟩ := H.halve ar hG
      (fun x => H.bun (H.bun H.emp P) (H.sg x) ∈ c) (by hdef) hle
    refine ⟨G', hG', hsub, fun B hB => ?_⟩
    have eB : B = H.emp := H.eq_emp fun z hz => by
      obtain ⟨j, hj, -⟩ := hB z hz
      rw [ar.iso.zero] at hj
      exact H.not_mem_emp j hj
    rw [eB]
    intro x y i j hx hy
    rcases hc with h | h
    · exact ⟨fun _ => h j y hy, fun _ => h i x hx⟩
    · exact ⟨fun h' => (h i x hx h').elim, fun h' => (h j y hy h').elim⟩
  · -- the step
    intro i ih P n L G K e1 e2 h1 h2 h3 hK hn hG
    obtain ⟨n0, rfl⟩ := ar.of_om hn
    obtain ⟨l, rfl⟩ := ar.of_om hG.2.1
    rw [ar.ex_iff.mp h1] at h2
    rw [ar.ex_iff.mp h2] at h3
    rw [ar.mu_iff.mp h3] at hK
    have hle : E (E i) * (E (E i) * n0) ≤ l := by
      have := ar.num_le.mp hK
      rwa [ar.nf.E_succ, ar.nf.E_add, mul_assoc] at this
    -- the pinned set for the tests that contain the new value
    obtain ⟨P1, hP1⟩ : ∃ P1, ∀ a, H.App A (num i) a → P1 = H.bun P (H.sg a) := by
      by_cases ha : ∃ a, H.App A (num i) a
      · obtain ⟨a, ha⟩ := ha
        exact ⟨H.bun P (H.sg a), fun a' ha' => by rw [hA.2 _ _ _ ha' ha]⟩
      · exact ⟨P, fun a ha' => (ha ⟨a, ha'⟩).elim⟩
    obtain ⟨G1, hG1, hs1, hc1⟩ := ih P1 (num (E (E i) * n0)) (num l) G
      (num (E (E i) * (E (E i) * n0))) (num (E i)) (num (E (E i)))
      (ar.ex_iff.mpr rfl) (ar.ex_iff.mpr rfl) (ar.mu_iff.mpr rfl) (ar.num_le.mpr hle)
      (ar.num_om _) hG
    obtain ⟨G2, hG2, hs2, hc2⟩ := ih P (num n0) (num (E (E i) * n0)) G1
      (num (E (E i) * n0)) (num (E i)) (num (E (E i)))
      (ar.ex_iff.mpr rfl) (ar.ex_iff.mpr rfl) (ar.mu_iff.mpr rfl) (Or.inr rfl)
      (ar.num_om _) hG1
    refine ⟨G2, hG2, hs2.trans hs1, fun B hB => ?_⟩
    by_cases hin : ∃ a, H.App A (num i) a ∧ a ∈ B
    · obtain ⟨a, ha, haB⟩ := hin
      obtain ⟨B', hB'⟩ := H.sep' B (fun z => z ≠ a) (by hdef)
      have hsB' : H.SubR B' A (num i) := fun b hb => by
        obtain ⟨hbB, hba⟩ := (hB' b).mp hb
        obtain ⟨j, hj, hjb⟩ := hB b hbB
        rw [ar.iso.succ] at hj
        rcases H.mem_suc.mp hj with h | h
        · exact ⟨j, h, hjb⟩
        · rw [h] at hjb
          exact (hba (hA.2 _ _ _ hjb ha)).elim
      have e : H.bun B P = H.bun B' P1 := by
        rw [hP1 a ha]
        refine H.ext' fun z => ?_
        simp only [H.mem_bun, H.mem_sg, hB' z]
        constructor
        · rintro (h | h)
          · by_cases e : z = a
            · exact Or.inr (Or.inr e)
            · exact Or.inl ⟨h, e⟩
          · exact Or.inr (Or.inl h)
        · rintro (⟨h, -⟩ | h | h)
          · exact Or.inl h
          · exact Or.inr h
          · rw [h]
            exact Or.inl haB
      rw [e]
      exact (hc1 B' hsB').sub hs2
    · refine hc2 B fun b hb => ?_
      obtain ⟨j, hj, hjb⟩ := hB b hb
      rw [ar.iso.succ] at hj
      rcases H.mem_suc.mp hj with h | h
      · exact ⟨j, h, hjb⟩
      · rw [h] at hjb
        exact (hin ⟨b, hjb, hb⟩).elim

end refine

end Host

/-! ## Phase 2 (A7, second part): pre-homogeneous sequences -/

namespace Host

variable {H : Host}

/-- The sequence without its first value. -/
theorem IncSeq.tail {f n : H.W} (hf : H.IncSeq f (H.suc n)) :
    ∃ g, H.IncSeq g n ∧ ∀ i a, H.App g i a ↔ H.App f (H.suc i) a := by
  have hn : n ∈ H.om := H.mem_om_of_mem hf.2.1 (H.mem_suc.mpr (Or.inr rfl))
  have hsuc : ∀ {i : H.W}, i ∈ n → H.suc i ∈ H.suc n := fun hi => by
    rcases H.suc_mem_or n hn _ hi with h | h
    · exact H.mem_suc.mpr (Or.inl h)
    · exact H.mem_suc.mpr (Or.inr h)
  have hpre : ∀ {i a : H.W}, H.App f (H.suc i) a → i ∈ n := fun {i a} h => by
    have hi : i ∈ H.suc i := H.mem_suc.mpr (Or.inr rfl)
    rcases H.mem_suc.mp (hf.dom h) with h1 | h1
    · exact H.om_mem_trans hn h1 hi
    · rw [← h1]
      exact hi
  have hfun : ∀ u ∈ n, ∀ v v', H.App f (H.suc u) v → H.App f (H.suc u) v' → v = v' :=
    fun u _ v v' h h' => hf.fn h h'
  refine ⟨H.mkFun n (fun i a => H.App f (H.suc i) a) (by hdef) hfun, ⟨⟨H.isFun_mkFun, fun i => ?_⟩,
    hn, fun i a h => hf.2.2.1 _ a (H.app_mkFun.mp h).2, fun i j a b h h' hij => ?_⟩, fun i a => ?_⟩
  · constructor
    · intro hi
      obtain ⟨a, ha⟩ := hf.tot (hsuc hi)
      exact ⟨a, H.app_mkFun.mpr ⟨hi, ha⟩⟩
    · rintro ⟨a, ha⟩
      exact (H.app_mkFun.mp ha).1
  · have hj := (H.app_mkFun.mp h').1
    have hjo := H.mem_om_of_mem hn hj
    refine hf.2.2.2 _ _ a b (H.app_mkFun.mp h).2 (H.app_mkFun.mp h').2 ?_
    rcases H.suc_mem_or j hjo i hij with h1 | h1
    · exact H.mem_suc.mpr (Or.inl h1)
    · exact H.mem_suc.mpr (Or.inr h1)
  · exact ⟨fun h => (H.app_mkFun.mp h).2, fun h => H.app_mkFun.mpr ⟨hpre h, h⟩⟩

/-- `B` is a set of values of `A`. -/
def SubV (B A : H.W) : Prop := ∀ b, b ∈ B → ∃ j, H.App A j b

/-- All members of `B` are members of (that is, numbers below) `x`. -/
def Below (B x : H.W) : Prop := ∀ b, b ∈ B → b ∈ x

/-- `A` is pre-homogeneous for `c`: whether `B ∪ {x} ∈ c`, for `B` a set of values of `A` and
`x` a value of `A` above `B`, does not depend on `x`. -/
def PreHom (c A : H.W) : Prop :=
  ∀ B x y i j, H.SubV B A → H.App A i x → H.App A j y → H.Below B x → H.Below B y →
    (H.bun B (H.sg x) ∈ c ↔ H.bun B (H.sg y) ∈ c)

/-- The same between the values of `A` or `G` and the values of `G`. -/
def Link (c A G : H.W) : Prop :=
  ∀ B x y j, H.SubV B A → ((∃ i, H.App A i x) ∨ ∃ i, H.App G i x) → H.App G j y → H.Below B x →
    (H.bun B (H.sg x) ∈ c ↔ H.bun B (H.sg y) ∈ c)

/-- Every value of `A` is below every value of `G`. -/
def Above (A G : H.W) : Prop := ∀ i a j x, H.App A i a → H.App G j x → a ∈ x

section prehom

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

theorem prehom_aux (ar : H.Arith E num) (c : H.W) (Nn : N) : ∀ j : N, ∀ (A i G L s t u : H.W),
    H.IncSeq A i → H.IncSeq G L → H.Above A G → H.PreHom c A → H.Link c A G →
    ar.Mu (num (E Nn)) (num j) t → ar.Ex t u → (u ∈ H.suc L ∨ u = H.suc L) →
    ar.Ad i (num j) s → (s ∈ num Nn ∨ s = num Nn) →
    ∃ A', H.IncSeq A' s ∧ H.PreHom c A' ∧
      ∀ k a, H.App A' k a → (∃ k', H.App A k' a) ∨ ∃ k', H.App G k' a := by
  have hE := ar.def_Ex
  have hM := ar.def_Mu
  have hD := ar.def_Ad
  have hdi := H.def_incSeq
  refine ar.num_ind (fun x => ∀ (A i G L s t u : H.W),
    H.IncSeq A i → H.IncSeq G L → H.Above A G → H.PreHom c A → H.Link c A G →
    ar.Mu (num (E Nn)) x t → ar.Ex t u → (u ∈ H.suc L ∨ u = H.suc L) →
    ar.Ad i x s → (s ∈ num Nn ∨ s = num Nn) →
    ∃ A', H.IncSeq A' s ∧ H.PreHom c A' ∧
      ∀ k a, H.App A' k a → (∃ k', H.App A k' a) ∨ ∃ k', H.App G k' a) (by hdef) ?_ ?_
  · intro A i G L s t u hA hG hab hph hlk _ _ _ had _
    obtain ⟨i0, rfl⟩ := ar.of_om hA.2.1
    rw [ar.ad_iff.mp had, add_zero]
    exact ⟨A, hA, hph, fun k a h => Or.inl ⟨k, h⟩⟩
  · intro j ih A i G L s t u hA hG hab hph hlk hmu hex hu had hs
    obtain ⟨i0, rfl⟩ := ar.of_om hA.2.1
    obtain ⟨l, rfl⟩ := ar.of_om hG.2.1
    rw [ar.mu_iff.mp hmu] at hex
    rw [ar.ex_iff.mp hex, ← ar.iso.succ] at hu
    rw [ar.ad_iff.mp had] at hs ⊢
    have hsz : E (E Nn * j) * E (E Nn) ≤ l + 1 := by
      have := ar.num_le.mp hu
      rwa [mul_add, mul_one, ar.nf.E_add] at this
    have hsN : i0 + (j + 1) ≤ Nn := ar.num_le.mp hs
    -- `E(E N)^j = n' + 1`
    obtain ⟨n', hn'⟩ : ∃ n', E (E Nn * j) = n' + 1 := by
      rcases ar.nf.zero_or_succ (E (E Nn * j)) with h | h
      · have := ar.nf.E_pos (E Nn * j)
        rw [h] at this
        exact (ar.nf.not_succ_le 0 (by rwa [zero_add])).elim
      · exact h
    have hW2 : (2 : N) ≤ E (E Nn) := by
      have := ar.nf.E_mono (ar.nf.E_pos Nn)
      rwa [ar.nf.E_one] at this
    -- `l = l' + 1`
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := by
      rcases ar.nf.zero_or_succ l with h | h
      · rw [h, hn', zero_add] at hsz
        have h2 : (2 : N) ≤ (n' + 1) * E (E Nn) := by
          have h3 := ar.nf.add_le_add_r (ar.nf.zero_le (n' * E (E Nn))) (E (E Nn))
          rw [zero_add] at h3
          have h4 : n' * E (E Nn) + E (E Nn) = (n' + 1) * E (E Nn) := by ring
          rw [h4] at h3
          exact le_trans hW2 h3
        have h5 : (1 : N) + 1 ≤ 1 := by
          have := le_trans h2 hsz
          rwa [← one_add_one_eq_two] at this
        exact (ar.nf.not_succ_le 1 h5).elim
      · exact h
    have hszW : E (E Nn) * n' ≤ l' := by
      rw [hn'] at hsz
      have h1 : E (E Nn) * n' + E (E Nn) ≤ l' + E (E Nn) := by
        have h2 : (n' + 1) * E (E Nn) = E (E Nn) * n' + E (E Nn) := by ring
        rw [h2] at hsz
        refine le_trans hsz ?_
        have h3 := ar.nf.add_le_add_l hW2 l'
        have h4 : l' + 1 + 1 = l' + 2 := by ring
        rw [h4]
        exact h3
      exact ar.nf.le_of_add_le_add_r h1
    -- the first value of `G`
    have h0l : num 0 ∈ num (l' + 1) := ar.num_mem.mpr (by
      rw [zero_add]
      have := ar.nf.add_le_add_r (ar.nf.zero_le l') 1
      rwa [zero_add] at this)
    obtain ⟨a, ha⟩ := hG.tot h0l
    have hao := hG.2.2.1 _ _ ha
    have hG' := hG
    rw [ar.iso.succ] at hG'
    obtain ⟨Gt, hGt, hGtm⟩ := hG'.tail
    have hGtG : H.SubSeq Gt G := fun k x hx => ⟨_, (hGtm k x).mp hx⟩
    have haGt : ∀ k x, H.App Gt k x → a ∈ x := fun k x hx => by
      obtain ⟨k0, rfl⟩ := ar.of_om (H.mem_om_of_mem hGt.2.1 (hGt.dom hx))
      refine hG.2.2.2 _ _ a x ha ((hGtm _ x).mp hx) ?_
      rw [← ar.iso.succ]
      exact ar.num_mem.mpr (by
        rw [zero_add]
        have := ar.nf.add_le_add_r (ar.nf.zero_le k0) 1
        rwa [zero_add] at this)
    -- the extended sequence
    have hA1 : H.IncSeq (H.ins A (num i0) a) (num (i0 + 1)) := by
      rw [ar.iso.succ]
      exact hA.snoc hao (fun k b hb => hab k b _ a hb ha)
    have hA1v : ∀ {k b : H.W}, H.App (H.ins A (num i0) a) k b → (∃ k', H.App A k' b) ∨ b = a :=
      fun h => (H.app_ins.mp h).elim (fun h => Or.inl ⟨_, h⟩) (fun h => Or.inr h.2)
    have hi1 : i0 + 1 ≤ Nn := le_trans (by
      have := ar.nf.le_add (i0 + 1) j
      have e : i0 + 1 + j = i0 + (j + 1) := by ring
      rwa [e] at this) hsN
    obtain ⟨G2, hG2, hG2s, hG2c⟩ := H.refine_lemma ar c (H.ins A (num i0) a) hA1.1.1
      (i0 + 1) n' l' H.emp Gt
      (le_trans (by
        have h1 := ar.nf.E_mono (ar.nf.E_mono hi1)
        have h2 := ar.nf.mul_le_mul_l h1 n'
        rwa [mul_comm n', mul_comm n'] at h2) hszW) hGt
    have hG2G : H.SubSeq G2 G := hG2s.trans hGtG
    -- a set of values of the extended sequence below a value of `A` is a set of values of `A`
    have hstar : ∀ {B z : H.W}, H.SubV B (H.ins A (num i0) a) → (∃ k, H.App A k z) → H.Below B z →
        H.SubV B A := fun {B z} hB ⟨k, hk⟩ hbel b hb => by
      obtain ⟨m, hm⟩ := hB b hb
      rcases hA1v hm with h | h
      · exact h
      · rw [h] at hb
        exact (H.mem_asymm (hbel a hb) (hab k z _ a hk ha)).elim
    have hstar' : ∀ {B : H.W}, H.SubV B (H.ins A (num i0) a) → H.Below B a → H.SubV B A :=
      fun {B} hB hbel b hb => by
        obtain ⟨m, hm⟩ := hB b hb
        rcases hA1v hm with h | h
        · exact h
        · rw [h] at hb
          exact (H.mem_irrefl a (hbel a hb)).elim
    have hAb1 : H.Above (H.ins A (num i0) a) G2 := by
      intro k b m x hb hx
      obtain ⟨m', hm'⟩ := hG2s m x hx
      rcases hA1v hb with ⟨k', h⟩ | h
      · obtain ⟨m'', hm''⟩ := hGtG m' x hm'
        exact hab k' b m'' x h hm''
      · rw [h]
        exact haGt m' x hm'
    have hPh1 : H.PreHom c (H.ins A (num i0) a) := by
      intro B x y i' j' hB hx hy hbx hby
      rcases hA1v hx with hx' | hx'
      · rcases hA1v hy with hy' | hy'
        · obtain ⟨k1, h1⟩ := hx'
          obtain ⟨k2, h2⟩ := hy'
          exact hph B x y k1 k2 (hstar hB ⟨k1, h1⟩ hbx) h1 h2 hbx hby
        · rw [hy']
          exact hlk B x a _ (hstar hB hx' hbx) (Or.inl hx') ha hbx
      · rcases hA1v hy with hy' | hy'
        · rw [hx']
          exact (hlk B y a _ (hstar hB hy' hby) (Or.inl hy') ha hby).symm
        · rw [hx', hy']
    have hLk1 : H.Link c (H.ins A (num i0) a) G2 := by
      intro B x y m hB hx hy hbx
      obtain ⟨m', hm'⟩ := hG2G m y hy
      rcases hx with ⟨k, hk⟩ | ⟨k, hk⟩
      · rcases hA1v hk with hx' | hx'
        · exact hlk B x y m' (hstar hB hx' hbx) (Or.inl hx') hm' hbx
        · rw [hx'] at hbx ⊢
          exact hlk B a y m' (hstar' hB hbx) (Or.inr ⟨_, ha⟩) hm' hbx
      · have hc := hG2c B (fun b hb => by
          obtain ⟨m1, hm1⟩ := hB b hb
          exact ⟨m1, hA1.dom hm1, hm1⟩)
        rw [H.bun_emp] at hc
        exact hc x y k m hk hy

    obtain ⟨A', hA', hph', hval⟩ := ih (H.ins A (num i0) a) (num (i0 + 1)) G2 (num n')
      (num (i0 + (j + 1))) (num (E Nn * j)) (num (E (E Nn * j))) hA1 hG2 hAb1 hPh1 hLk1
      (ar.mu_iff.mpr rfl) (ar.ex_iff.mpr rfl) (Or.inr (by rw [← ar.iso.succ, hn']))
      (ar.ad_iff.mpr (by congr 1; ring)) hs
    refine ⟨A', hA', hph', fun k b hb => ?_⟩
    rcases hval k b hb with ⟨k', h⟩ | ⟨k', h⟩
    · rcases hA1v h with h1 | h1
      · exact Or.inl h1
      · rw [h1]
        exact Or.inr ⟨_, ha⟩
    · exact Or.inr (hG2G k' b h)

/-- **Pre-homogeneous sequences exist.** From an increasing sequence of length
`2 · E(E(n) · n)` one can select a pre-homogeneous increasing sequence of length `n`. -/
theorem exists_prehom (ar : H.Arith E num) (c : H.W) {n l : N} {F : H.W}
    (hF : H.IncSeq F (num l)) (hl : E (E n * n) + E (E n * n) ≤ l) :
    ∃ A, H.IncSeq A (num n) ∧ H.SubSeq A F ∧ H.PreHom c A := by
  obtain ⟨G, hG, hGs, hGc⟩ := H.refine_lemma ar c H.emp H.isFun_emp 0 (E (E n * n)) l H.emp F
    (by rwa [ar.nf.E_zero, ar.nf.E_one, two_mul]) hF
  have hnone : ∀ {B : H.W}, H.SubV B H.emp → B = H.emp := fun hB =>
    H.eq_emp fun z hz => by
      obtain ⟨j, hj⟩ := hB z hz
      exact H.not_mem_emp _ (H.app_iff.mp hj)
  obtain ⟨A, hA, hph, hval⟩ := H.prehom_aux ar c n n H.emp (num 0) G (num (E (E n * n)))
    (num (0 + n)) (num (E n * n)) (num (E (E n * n)))
    (by rw [ar.iso.zero]; exact H.incSeq_emp) hG
    (fun i a j x h => (H.not_mem_emp _ (H.app_iff.mp h)).elim)
    (fun B x y i j _ h => (H.not_mem_emp _ (H.app_iff.mp h)).elim)
    (fun B x y j hB hx hy _ => by
      rcases hx with ⟨i, h⟩ | ⟨i, h⟩
      · exact (H.not_mem_emp _ (H.app_iff.mp h)).elim
      · have hc := hGc B (fun b hb => by rw [hnone hB] at hb; exact (H.not_mem_emp b hb).elim)
        rw [H.bun_emp] at hc
        exact hc x y i j h hy)
    (ar.mu_iff.mpr rfl) (ar.ex_iff.mpr rfl)
    (Or.inl (by rw [← ar.iso.succ]; exact ar.num_mem.mpr (le_refl _)))
    (ar.ad_iff.mpr rfl) (Or.inr (by rw [zero_add]))
  rw [zero_add] at hA
  refine ⟨A, hA, fun k a hk => ?_, hph⟩
  rcases hval k a hk with ⟨k', h⟩ | ⟨k', h⟩
  · exact (H.not_mem_emp _ (H.app_iff.mp h)).elim
  · exact hGs k' a h

end prehom

end Host

/-! ## Phase 2 (A7, third part): Ramsey's theorem with a variable exponent -/

namespace Host

variable {H : Host}

/-- `B` is a set of `r` numbers: the set of the values of an increasing sequence of length
`r`. -/
def Card (B r : H.W) : Prop := ∃ s, H.IncSeq s r ∧ ∀ z, z ∈ B ↔ ∃ i, H.App s i z

theorem def_card : Def2 H (fun B r => H.Card B r) := by
  have := H.def_incSeq
  hdef

/-- `g` is homogeneous for `c` on the sets of `r` of its values. -/
def Hom (c r g : H.W) : Prop :=
  ∀ B B', H.Card B r → H.Card B' r → H.SubV B g → H.SubV B' g → (B ∈ c ↔ B' ∈ c)

/-- Every increasing sequence of length `Q` has, for every set `c`, an increasing subsequence
of length `q` that is homogeneous for `c` on sets of `r` values. -/
def Ram (r q Q : H.W) : Prop :=
  ∀ c F, H.IncSeq F Q → ∃ g, H.IncSeq g q ∧ H.SubSeq g F ∧ H.Hom c r g

/-- One step of the bound: `x ↦ 2 · E(E(x + 1) · (x + 1))`. -/
def rstep {N : Type} [CommSemiring N] (E : N → N) (x : N) : N :=
  E (E (x + 1) * (x + 1)) + E (E (x + 1) * (x + 1))

section ramsey

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- The graph of `rstep` on the numbers of the host. -/
def Arith.RStep (ar : H.Arith E num) (x y : H.W) : Prop :=
  ∃ n e t u, n = H.suc x ∧ ar.Ex n e ∧ ar.Mu e n t ∧ ar.Ex t u ∧ ar.Ad u u y

theorem Arith.rstep_iff (ar : H.Arith E num) {x : N} {y : H.W} :
    ar.RStep (num x) y ↔ y = num (rstep E x) := by
  constructor
  · rintro ⟨n, e, t, u, rfl, h1, h2, h3, h4⟩
    rw [← ar.iso.succ] at h1 h2
    rw [ar.ex_iff.mp h1] at h2
    rw [ar.mu_iff.mp h2] at h3
    rw [ar.ex_iff.mp h3] at h4
    exact ar.ad_iff.mp h4
  · rintro rfl
    exact ⟨num (x + 1), num (E (x + 1)), num (E (x + 1) * (x + 1)),
      num (E (E (x + 1) * (x + 1))), ar.iso.succ x, ar.ex_iff.mpr rfl, ar.mu_iff.mpr rfl,
      ar.ex_iff.mpr rfl, ar.ad_iff.mpr rfl⟩

/-- `Q` is the bound for the exponent `r` and the length `q`: the result of applying `rstep`
`r` times to `q`. -/
def Arith.RamB (ar : H.Arith E num) (r q Q : H.W) : Prop :=
  ∃ b, H.FunOn b (H.suc r) ∧ (∀ i y, H.App b i y → y ∈ H.om) ∧ H.App b H.emp q ∧
    (∀ i x y, i ∈ r → H.App b i x → H.App b (H.suc i) y → ar.RStep x y) ∧ H.App b r Q

theorem Arith.def_ramB (ar : H.Arith E num) : Def3 H ar.RamB := by
  have h1 := ar.def_Ex
  have h2 := ar.def_Mu
  have h3 := ar.def_Ad
  hdef

theorem Arith.ramB_zero (ar : H.Arith E num) {q Q : H.W} (h : ar.RamB (num 0) q Q) : Q = q := by
  obtain ⟨b, hb, -, h0, -, hQ⟩ := h
  rw [ar.iso.zero] at hQ
  exact hb.1.2 _ _ _ hQ h0

theorem Arith.ramB_zero_intro (ar : H.Arith E num) {q : H.W} (hq : q ∈ H.om) :
    ar.RamB (num 0) q q := by
  rw [ar.iso.zero]
  refine ⟨H.ins H.emp H.emp q, H.funOn_ins H.funOn_emp, fun i y h => ?_,
    H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩), fun i x y hi => (H.not_mem_emp i hi).elim,
    H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩)⟩
  rcases H.app_ins.mp h with h1 | ⟨-, h1⟩
  · exact (H.not_mem_emp _ (H.app_iff.mp h1)).elim
  · rw [h1]
    exact hq

theorem Arith.ramB_succ (ar : H.Arith E num) {r : N} {q Q' : H.W}
    (h : ar.RamB (num (r + 1)) q Q') :
    ∃ Q0 : N, ar.RamB (num r) q (num Q0) ∧ Q' = num (rstep E Q0) := by
  obtain ⟨b, hb, hom, h0, hstep, hQ⟩ := h
  rw [ar.iso.succ] at hb hstep hQ
  have hr1 : num r ∈ H.suc (num r) := H.mem_suc.mpr (Or.inr rfl)
  obtain ⟨Q, hQr⟩ := (hb.2 (num r)).mp (H.mem_suc.mpr (Or.inl hr1))
  obtain ⟨Q0, rfl⟩ := ar.of_om (hom _ _ hQr)
  refine ⟨Q0, ⟨H.res b (H.suc (num r)), H.funOn_res hb (fun z hz => H.mem_suc.mpr (Or.inl hz)),
    fun i y h => hom i y (H.app_res.mp h).2, H.app_res.mpr ⟨?_, h0⟩,
    fun i x y hi hx hy => hstep i x y (H.mem_suc.mpr (Or.inl hi)) (H.app_res.mp hx).2
      (H.app_res.mp hy).2, H.app_res.mpr ⟨hr1, hQr⟩⟩,
    ar.rstep_iff.mp (hstep (num r) _ _ hr1 hQr hQ)⟩
  rcases H.emp_mem_or (H.suc_mem_om (ar.num_om r)) with h | h
  · exact (H.suc_ne_emp _ h).elim
  · exact h

theorem Arith.ramB_succ_intro (ar : H.Arith E num) {r Q0 : N} {q : H.W}
    (h : ar.RamB (num r) q (num Q0)) : ar.RamB (num (r + 1)) q (num (rstep E Q0)) := by
  obtain ⟨b, hb, hom, h0, hstep, hQ⟩ := h
  rw [ar.iso.succ]
  have hnot : ∀ {i : H.W}, i ∈ H.suc (num r) → i ≠ H.suc (num r) := fun hi e =>
    H.mem_irrefl _ (e ▸ hi)
  refine ⟨H.ins b (H.suc (num r)) (num (rstep E Q0)), H.funOn_ins hb, fun i y h => ?_,
    H.app_ins.mpr (Or.inl h0), fun i x y hi hx hy => ?_, H.app_ins.mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · rcases H.app_ins.mp h with h1 | ⟨-, h1⟩
    · exact hom i y h1
    · rw [h1]
      exact ar.num_om _
  · have hx' : H.App b i x := by
      rcases H.app_ins.mp hx with h1 | ⟨h1, -⟩
      · exact h1
      · exact (hnot hi h1).elim
    rcases H.mem_suc.mp hi with hi' | hi'
    · have hy' : H.App b (H.suc i) y := by
        rcases H.app_ins.mp hy with h1 | ⟨h1, -⟩
        · exact h1
        · rw [H.suc_inj h1] at hi'
          exact (H.mem_irrefl _ hi').elim
      exact hstep i x y hi' hx' hy'
    · rw [hi'] at hx' hy
      rw [hb.1.2 _ _ _ hx' hQ]
      rcases H.app_ins.mp hy with h1 | ⟨-, h1⟩
      · exact (H.mem_irrefl _ ((hb.2 _).mpr ⟨y, h1⟩)).elim
      · rw [h1]
        exact ar.rstep_iff.mpr rfl

/-- **Ramsey's theorem** in a host, for every exponent that is a number of the host, with the
bound obtained by iterating `rstep`. -/
theorem ramsey (ar : H.Arith E num) :
    ∀ r : N, ∀ q Q : H.W, q ∈ H.om → ar.RamB (num r) q Q → H.Ram (num r) q Q := by
  have hB := ar.def_ramB
  have hdi := H.def_incSeq
  have hdc := H.def_card
  refine ar.num_ind (fun x => ∀ q Q, q ∈ H.om → ar.RamB x q Q → H.Ram x q Q) (by hdef) ?_ ?_
  · intro q Q hq hb c F hF
    rw [ar.ramB_zero hb] at hF
    have hemp : ∀ {B : H.W}, H.Card B (num 0) → B = H.emp := fun {B} ⟨s, hs, hsm⟩ =>
      H.eq_emp fun z hz => by
        obtain ⟨i, hi⟩ := (hsm z).mp hz
        have := hs.dom hi
        rw [ar.iso.zero] at this
        exact H.not_mem_emp i this
    exact ⟨F, hF, fun i a h => ⟨i, h⟩, fun B B' hB hB' _ _ => by rw [hemp hB, hemp hB']⟩
  · intro r ih q Q' hq hb c F hF
    obtain ⟨Q0, hb0, rfl⟩ := ar.ramB_succ hb
    obtain ⟨A, hA, hAF, hph⟩ := H.exists_prehom ar c (n := Q0 + 1) hF (le_of_eq rfl)
    have hlastdom : num Q0 ∈ num (Q0 + 1) := ar.num_mem.mpr (le_refl _)
    obtain ⟨last, hlast⟩ := hA.tot hlastdom
    have hA' := hA.res (ar.num_om Q0) (ar.num_sub (ar.nf.le_add Q0 1))
    obtain ⟨c1, hc1⟩ := H.sep' c (fun B => last ∈ B) (by hdef)
    obtain ⟨c', hc'⟩ := H.repl' c1 (fun Bp B => ∀ z, z ∈ B ↔ z ∈ Bp ∧ z ≠ last) (by hdef)
      (fun u _ v v' h h' => H.ext' fun z => (h z).trans (h' z).symm)
    have hc'iff : ∀ B, ¬ last ∈ B → (B ∈ c' ↔ H.bun B (H.sg last) ∈ c) := by
      intro B hB
      rw [hc' B]
      constructor
      · rintro ⟨Bp, hBp, hrel⟩
        obtain ⟨hBpc, hl⟩ := (hc1 Bp).mp hBp
        have e : H.bun B (H.sg last) = Bp := H.ext' fun z => by
          rw [H.mem_bun, H.mem_sg, hrel z]
          constructor
          · rintro (h | h)
            · exact h.1
            · rw [h]
              exact hl
          · intro h
            by_cases e : z = last
            · exact Or.inr e
            · exact Or.inl ⟨h, e⟩
        rw [e]
        exact hBpc
      · intro h
        refine ⟨H.bun B (H.sg last),
          (hc1 _).mpr ⟨h, H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl))⟩, fun z => ?_⟩
        rw [H.mem_bun, H.mem_sg]
        constructor
        · intro hz
          exact ⟨Or.inl hz, fun e => hB (e ▸ hz)⟩
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact (h2 h1).elim
    obtain ⟨g, hg, hgA', hhom⟩ := ih q (num Q0) hq hb0 c' (H.res A (num Q0)) hA'
    have hgl : ∀ i a, H.App g i a → (∃ j, H.App A j a) ∧ a ∈ last := fun i a h => by
      obtain ⟨j, hj⟩ := hgA' i a h
      obtain ⟨hjd, hja⟩ := H.app_res.mp hj
      exact ⟨⟨j, hja⟩, hA.2.2.2 j (num Q0) a last hja hlast hjd⟩
    refine ⟨g, hg, fun i a h => ?_, ?_⟩
    · obtain ⟨⟨j, hj⟩, -⟩ := hgl i a h
      exact hAF j a hj
    have key : ∀ B, H.Card B (num (r + 1)) → H.SubV B g →
        ∃ B0, H.Card B0 (num r) ∧ H.SubV B0 g ∧ (B ∈ c ↔ B0 ∈ c') := by
      rintro B ⟨s, hs, hsm⟩ hBg
      have hrd : num r ∈ num (r + 1) := ar.num_mem.mpr (le_refl _)
      obtain ⟨x, hx⟩ := hs.tot hrd
      have hs0 := hs.res (ar.num_om r) (ar.num_sub (ar.nf.le_add r 1))
      obtain ⟨B0, hB0⟩ := H.sep' B (fun z => z ≠ x) (by hdef)
      have hB0m : ∀ z, z ∈ B0 ↔ ∃ i, H.App (H.res s (num r)) i z := by
        intro z
        rw [hB0 z, hsm z]
        constructor
        · rintro ⟨⟨i, hi⟩, hne⟩
          have hid := hs.dom hi
          rw [ar.iso.succ] at hid
          rcases H.mem_suc.mp hid with h | h
          · exact ⟨i, H.app_res.mpr ⟨h, hi⟩⟩
          · rw [h] at hi
            exact (hne (hs.fn hi hx)).elim
        · rintro ⟨i, hi⟩
          obtain ⟨hid, hi'⟩ := H.app_res.mp hi
          refine ⟨⟨i, hi'⟩, fun e => ?_⟩
          rw [e] at hi'
          exact H.mem_irrefl x (hs.2.2.2 i (num r) x x hi' hx hid)
      have hxB : x ∈ B := (hsm x).mpr ⟨_, hx⟩
      have hB0g : H.SubV B0 g := fun b hb => hBg b ((hB0 b).mp hb).1
      have hbel : H.Below B0 x := fun b hb => by
        obtain ⟨i, hi⟩ := (hB0m b).mp hb
        obtain ⟨hid, hi'⟩ := H.app_res.mp hi
        exact hs.2.2.2 i (num r) b x hi' hx hid
      have eB : B = H.bun B0 (H.sg x) := H.ext' fun z => by
        rw [H.mem_bun, H.mem_sg, hB0 z]
        constructor
        · intro h
          by_cases e : z = x
          · exact Or.inr e
          · exact Or.inl ⟨h, e⟩
        · rintro (h | h)
          · exact h.1
          · rw [h]
            exact hxB
      obtain ⟨jx, hjx⟩ := hBg x hxB
      obtain ⟨⟨kx, hkx⟩, hxl⟩ := hgl jx x hjx
      have hB0A : H.SubV B0 A := fun b hb => by
        obtain ⟨j, hj⟩ := hB0g b hb
        exact (hgl j b hj).1
      have hbl : H.Below B0 last := fun b hb => by
        obtain ⟨j, hj⟩ := hB0g b hb
        exact (hgl j b hj).2
      have hnl : ¬ last ∈ B0 := fun h => H.mem_irrefl last (hbl last h)
      refine ⟨B0, ⟨_, hs0, hB0m⟩, hB0g, ?_⟩
      rw [eB, hc'iff B0 hnl]
      exact hph B0 x last kx (num Q0) hB0A hkx hlast hbel hbl
    intro B B' hB hB' hBg hB'g
    obtain ⟨B0, h1, h2, h3⟩ := key B hB hBg
    obtain ⟨B0', h1', h2', h3'⟩ := key B' hB' hB'g
    rw [h3, h3']
    exact hhom B0 B0' h1 h1' h2 h2'

end ramsey

end Host

/-! ## Phase 2 (A2–A3): flat models in a host, terms as numbers, the selection conditions -/

/-- **A flat model in a host.** The levels are the numbers `1, …, d` of the host. `Ob x a`:
`x` is an object of the level `a`. `El z x (op a b)`: the object `z` of the level `b` is a
member of the object `x` of the level `a`, for `b` below `a`. The axioms are extensionality
and the typed forms, for every descending chain of levels, of the existence axioms. -/
structure FlatM (H : Host) where
  d : H.W
  Ob : H.W → H.W → Prop
  El : H.W → H.W → H.W → Prop
  hd : d ∈ H.om
  defOb : Def2 H Ob
  defEl : Def3 H El

namespace FlatM

variable {H : Host} (Fm : FlatM H)

/-- `a` is a level. -/
def Lv (a : H.W) : Prop := a ∈ H.suc Fm.d ∧ a ≠ H.emp

/-- `b` is a level below the level `a`. -/
def Lt (b a : H.W) : Prop := Fm.Lv a ∧ b ∈ a ∧ b ≠ H.emp

/-- `s` is the singleton, at the level `a`, of the object `x` of the level `b`. -/
def IsSg (a b x s : H.W) : Prop :=
  Fm.Ob s a ∧ ∀ z, Fm.Ob z b → (Fm.El z s (H.op a b) ↔ z = x)

/-- `p` is the pair, at the level `a`, of the objects `x`, `y` of the level `b`. -/
def IsUp (a b x y p : H.W) : Prop :=
  Fm.Ob p a ∧ ∀ z, Fm.Ob z b → (Fm.El z p (H.op a b) ↔ z = x ∨ z = y)

/-- `p` is the ordered pair, at the level `a` through the level `b`, of the objects `x`, `y`
of the level `c`. -/
def IsOp (a b c x y p : H.W) : Prop :=
  ∃ s u, Fm.IsSg b c x s ∧ Fm.IsUp b c x y u ∧ Fm.IsUp a b s u p

/-- The axioms of a flat model. -/
structure Ax : Prop where
  lv_ob : ∀ a x, Fm.Ob x a → Fm.Lv a
  ne : ∀ a, Fm.Lv a → ∃ x, Fm.Ob x a
  ext : ∀ a b x y, Fm.Lt b a → Fm.Ob x a → Fm.Ob y a →
    (∀ z, Fm.Ob z b → (Fm.El z x (H.op a b) ↔ Fm.El z y (H.op a b))) → x = y
  sing : ∀ a b x, Fm.Lt b a → Fm.Ob x b → ∃ s, Fm.IsSg a b x s
  up : ∀ a b x y, Fm.Lt b a → Fm.Ob x b → Fm.Ob y b → ∃ p, Fm.IsUp a b x y p
  inter : ∀ a b x y, Fm.Lt b a → Fm.Ob x a → Fm.Ob y a → ∃ w, Fm.Ob w a ∧ ∀ z, Fm.Ob z b →
    (Fm.El z w (H.op a b) ↔ Fm.El z x (H.op a b) ∧ Fm.El z y (H.op a b))
  compl : ∀ a b x, Fm.Lt b a → Fm.Ob x a → ∃ w, Fm.Ob w a ∧ ∀ z, Fm.Ob z b →
    (Fm.El z w (H.op a b) ↔ ¬ Fm.El z x (H.op a b))
  cardinalOne : ∀ a b c, Fm.Lt b a → Fm.Lt c b → ∃ y, Fm.Ob y a ∧ ∀ p, Fm.Ob p b →
    (Fm.El p y (H.op a b) ↔ ∃ q, Fm.Ob q c ∧ Fm.IsSg b c q p)
  vCross : ∀ a b c e x, Fm.Lt b a → Fm.Lt c b → Fm.Lt e c → Fm.Ob x c →
    ∃ y, Fm.Ob y a ∧ ∀ p, Fm.Ob p b → (Fm.El p y (H.op a b) ↔
      ∃ q r, Fm.Ob q e ∧ Fm.Ob r e ∧ Fm.IsOp b c e q r p ∧ Fm.El r x (H.op c e))
  converse : ∀ a b c e x, Fm.Lt b a → Fm.Lt c b → Fm.Lt e c → Fm.Ob x a →
    ∃ y, Fm.Ob y a ∧ ∀ p q r r', Fm.Ob p e → Fm.Ob q e → Fm.IsOp b c e p q r →
      Fm.IsOp b c e q p r' → (Fm.El r y (H.op a b) ↔ Fm.El r' x (H.op a b))
  subset : ∀ a b c e g, Fm.Lt b a → Fm.Lt c b → Fm.Lt e c → Fm.Lt g e →
    ∃ y, Fm.Ob y a ∧ ∀ p q o, Fm.Ob p e → Fm.Ob q e → Fm.IsOp b c e p q o →
      (Fm.El o y (H.op a b) ↔ ∀ r, Fm.Ob r g → Fm.El r p (H.op e g) → Fm.El r q (H.op e g))
  singletonImage : ∀ a b c e g x, Fm.Lt b a → Fm.Lt c b → Fm.Lt e c → Fm.Lt g e → Fm.Ob x b →
    ∃ y, Fm.Ob y a ∧ ∀ z w sz sw P Q, Fm.Ob z g → Fm.Ob w g → Fm.IsSg e g z sz →
      Fm.IsSg e g w sw → Fm.IsOp b c e sz sw P → Fm.IsOp c e g z w Q →
      (Fm.El P y (H.op a b) ↔ Fm.El Q x (H.op b c))
  insertion2 : ∀ a b c e g h x, Fm.Lt b a → Fm.Lt c b → Fm.Lt e c → Fm.Lt g e → Fm.Lt h g →
    Fm.Ob x c → ∃ y, Fm.Ob y a ∧ ∀ p q r sp ssp oqr P opr, Fm.Ob p h → Fm.Ob q h → Fm.Ob r h →
      Fm.IsSg g h p sp → Fm.IsSg e g sp ssp → Fm.IsOp e g h q r oqr → Fm.IsOp b c e ssp oqr P →
      Fm.IsOp e g h p r opr → (Fm.El P y (H.op a b) ↔ Fm.El opr x (H.op c e))
  insertion3 : ∀ a b c e g h x, Fm.Lt b a → Fm.Lt c b → Fm.Lt e c → Fm.Lt g e → Fm.Lt h g →
    Fm.Ob x c → ∃ y, Fm.Ob y a ∧ ∀ p q r sp ssp oqr P opq, Fm.Ob p h → Fm.Ob q h → Fm.Ob r h →
      Fm.IsSg g h p sp → Fm.IsSg e g sp ssp → Fm.IsOp e g h q r oqr → Fm.IsOp b c e ssp oqr P →
      Fm.IsOp e g h p q opq → (Fm.El P y (H.op a b) ↔ Fm.El opq x (H.op c e))
  typeLower : ∀ a b c e g x, Fm.Lt b a → Fm.Lt c b → Fm.Lt e c → Fm.Lt g e → Fm.Ob x a →
    ∃ y, Fm.Ob y e ∧ ∀ p, Fm.Ob p g → (Fm.El p y (H.op e g) ↔
      ∀ q sp P, Fm.Ob q e → Fm.IsSg e g p sp → Fm.IsOp b c e q sp P → Fm.El P x (H.op a b))

variable {Fm}

theorem lt_trans {a b c : H.W} (h1 : Fm.Lt b a) (h2 : Fm.Lt c b) : Fm.Lt c a :=
  ⟨h1.1, H.om_mem_trans (H.mem_om_of_mem (H.suc_mem_om Fm.hd) h1.1.1) h1.2.1 h2.2.1, h2.2.2⟩

theorem Lt.lv {a b : H.W} (h : Fm.Lt b a) : Fm.Lv b :=
  ⟨H.om_mem_trans (H.suc_mem_om Fm.hd) h.1.1 h.2.1, h.2.2⟩

variable (ax : Fm.Ax)
include ax

theorem sg_unique {a b x s s' : H.W} (hlt : Fm.Lt b a) (h : Fm.IsSg a b x s)
    (h' : Fm.IsSg a b x s') : s = s' :=
  ax.ext a b s s' hlt h.1 h'.1 fun z hz => (h.2 z hz).trans (h'.2 z hz).symm

theorem up_unique {a b x y p p' : H.W} (hlt : Fm.Lt b a) (h : Fm.IsUp a b x y p)
    (h' : Fm.IsUp a b x y p') : p = p' :=
  ax.ext a b p p' hlt h.1 h'.1 fun z hz => (h.2 z hz).trans (h'.2 z hz).symm

theorem sg_inj {a b x x' s : H.W} (hx : Fm.Ob x b) (h : Fm.IsSg a b x s)
    (h' : Fm.IsSg a b x' s) : x = x' := (h'.2 x hx).mp ((h.2 x hx).mpr rfl)

theorem op_ex {a b c x y : H.W} (h1 : Fm.Lt b a) (h2 : Fm.Lt c b) (hx : Fm.Ob x c)
    (hy : Fm.Ob y c) : ∃ p, Fm.IsOp a b c x y p := by
  obtain ⟨s, hs⟩ := ax.sing b c x h2 hx
  obtain ⟨u, hu⟩ := ax.up b c x y h2 hx hy
  obtain ⟨p, hp⟩ := ax.up a b s u h1 hs.1 hu.1
  exact ⟨p, s, u, hs, hu, hp⟩

theorem op_unique {a b c x y p p' : H.W} (h1 : Fm.Lt b a) (h2 : Fm.Lt c b)
    (h : Fm.IsOp a b c x y p) (h' : Fm.IsOp a b c x y p') : p = p' := by
  obtain ⟨s, u, hs, hu, hp⟩ := h
  obtain ⟨s', u', hs', hu', hp'⟩ := h'
  rw [FlatM.sg_unique ax h2 hs' hs, FlatM.up_unique ax h2 hu' hu] at hp'
  exact FlatM.up_unique ax h1 hp hp'

theorem op_ob {a b c x y p : H.W} (h : Fm.IsOp a b c x y p) : Fm.Ob p a := by
  obtain ⟨s, u, -, -, hp⟩ := h
  exact hp.1

/-- Ordered pairs determine their components. -/
theorem op_inj {a b c x y x' y' p : H.W} (hx : Fm.Ob x c)
    (hy : Fm.Ob y c) (hx' : Fm.Ob x' c) (hy' : Fm.Ob y' c) (h : Fm.IsOp a b c x y p)
    (h' : Fm.IsOp a b c x' y' p) : x = x' ∧ y = y' := by
  obtain ⟨s, u, hs, hu, hp⟩ := h
  obtain ⟨s', u', hs', hu', hp'⟩ := h'
  have e1 : s = s' ∨ s = u' := (hp'.2 s hs.1).mp ((hp.2 s hs.1).mpr (Or.inl rfl))
  have exx : x = x' := by
    rcases e1 with e | e
    · have h1 : Fm.El x s' (H.op b c) := by
        rw [← e]
        exact (hs.2 x hx).mpr rfl
      exact (hs'.2 x hx).mp h1
    · have h1 : Fm.El x' s (H.op b c) := by
        rw [e]
        exact (hu'.2 x' hx').mpr (Or.inl rfl)
      exact ((hs.2 x' hx').mp h1).symm
  subst exx
  have e2 : u = s' ∨ u = u' := (hp'.2 u hu.1).mp ((hp.2 u hu.1).mpr (Or.inr rfl))
  have e3 : u' = s ∨ u' = u := (hp.2 u' hu'.1).mp ((hp'.2 u' hu'.1).mpr (Or.inr rfl))
  have hyu : Fm.El y u (H.op b c) := (hu.2 y hy).mpr (Or.inr rfl)
  have hy'u' : Fm.El y' u' (H.op b c) := (hu'.2 y' hy').mpr (Or.inr rfl)
  refine ⟨rfl, ?_⟩
  rcases e2 with e | e
  · have hyx : y = x := by
      rw [e] at hyu
      exact (hs'.2 y hy).mp hyu
    rcases e3 with e' | e'
    · rw [e'] at hy'u'
      rw [hyx, (hs.2 y' hy').mp hy'u']
    · rw [e'] at hy'u'
      rcases (hu.2 y' hy').mp hy'u' with h | h
      · rw [hyx, h]
      · exact h.symm
  · rw [e] at hyu
    rcases (hu'.2 y hy).mp hyu with h | h
    · rw [← e] at hy'u'
      rcases (hu.2 y' hy').mp hy'u' with h' | h'
      · rw [h, h']
      · exact h'.symm
    · exact h

end FlatM

/-! ## Phase 2 (A2–A3): terms as numbers and the selection conditions

Every symbol is binary. The term with the tag `f` and the arguments `x`, `y` has the code
`tm f x y = ⟨f, ⟨x, y⟩⟩ + 1`; every other number is the null term. The tags are:
0 sing, 1 up, 2 IN, 3 CO, 4 SI, 5 I2, 6 I3, 7 VC, 8 TL, 9 CV, 10 C1, 11 SB, 12 D, 13 P1, 14 P2,
15 EL, 16 WT, 17 WS. -/

/-- The pairing function on a structure of numbers. -/
def npair {N : Type} [CommSemiring N] (x y : N) : N := (x + y) * (x + y) + x

/-- The code of the term with the tag `f` and the arguments `x`, `y`. -/
def tm {N : Type} [CommSemiring N] (f : ℕ) (x y : N) : N := npair (f : N) (npair x y) + 1

namespace Host

/-! ### The levels around a position of a placement -/

def L0 (H : Host) (v k a : H.W) : Prop := H.App v k a
def Lm1 (H : Host) (v k a : H.W) : Prop := ∃ k1, k = H.suc k1 ∧ H.App v k1 a
def Lm2 (H : Host) (v k a : H.W) : Prop := ∃ k1, k = H.suc k1 ∧ H.Lm1 v k1 a
def Lm3 (H : Host) (v k a : H.W) : Prop := ∃ k1, k = H.suc k1 ∧ H.Lm2 v k1 a
def Lm4 (H : Host) (v k a : H.W) : Prop := ∃ k1, k = H.suc k1 ∧ H.Lm3 v k1 a
def Lm5 (H : Host) (v k a : H.W) : Prop := ∃ k1, k = H.suc k1 ∧ H.Lm4 v k1 a
def Lp1 (H : Host) (v k a : H.W) : Prop := H.App v (H.suc k) a
def Lp2 (H : Host) (v k a : H.W) : Prop := H.App v (H.suc (H.suc k)) a
def Lp3 (H : Host) (v k a : H.W) : Prop := H.App v (H.suc (H.suc (H.suc k))) a

end Host

namespace FlatM

variable {H : Host} (Fm : FlatM H)

/-! ### The selection conditions of the eighteen symbols -/

/-- The selection condition of the symbol `sing`. -/
def T0 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1, H.L0 v k a ∧ H.Lm1 v k a1 ∧
    Fm.IsSg a a1 c1 y

/-- The selection condition of the symbol `up`. -/
def T1 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1, H.L0 v k a ∧ H.Lm1 v k a1 ∧
    Fm.IsUp a a1 c1 c2 y

/-- The selection condition of the symbol `IN`. -/
def T2 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1, H.L0 v k a ∧ H.Lm1 v k a1 ∧
    Fm.Ob y a ∧ ∀ z, Fm.Ob z a1 → (Fm.El z y (H.op a a1) ↔
      Fm.El z c1 (H.op a a1) ∧ Fm.El z c2 (H.op a a1))

/-- The selection condition of the symbol `CO`. -/
def T3 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1, H.L0 v k a ∧ H.Lm1 v k a1 ∧
    Fm.Ob y a ∧ ∀ z, Fm.Ob z a1 → (Fm.El z y (H.op a a1) ↔ ¬ Fm.El z c1 (H.op a a1))

/-- The selection condition of the symbol `SI`. -/
def T4 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 a2 a3 a4, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lm2 v k a2 ∧ H.Lm3 v k a3 ∧ H.Lm4 v k a4 ∧
    Fm.Ob y a ∧ ∀ z w sz sw P Q, Fm.Ob z a4 → Fm.Ob w a4 → Fm.IsSg a3 a4 z sz →
      Fm.IsSg a3 a4 w sw → Fm.IsOp a1 a2 a3 sz sw P → Fm.IsOp a2 a3 a4 z w Q →
      (Fm.El P y (H.op a a1) ↔ Fm.El Q c1 (H.op a1 a2))

/-- The selection condition of the symbol `I2`. -/
def T5 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 a2 a3 a4 a5, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lm2 v k a2 ∧ H.Lm3 v k a3 ∧ H.Lm4 v k a4 ∧ H.Lm5 v k a5 ∧
    Fm.Ob y a ∧ ∀ p q r sp ssp oqr P opr, Fm.Ob p a5 → Fm.Ob q a5 → Fm.Ob r a5 →
      Fm.IsSg a4 a5 p sp → Fm.IsSg a3 a4 sp ssp → Fm.IsOp a3 a4 a5 q r oqr →
      Fm.IsOp a1 a2 a3 ssp oqr P → Fm.IsOp a3 a4 a5 p r opr →
      (Fm.El P y (H.op a a1) ↔ Fm.El opr c1 (H.op a2 a3))

/-- The selection condition of the symbol `I3`. -/
def T6 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 a2 a3 a4 a5, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lm2 v k a2 ∧ H.Lm3 v k a3 ∧ H.Lm4 v k a4 ∧ H.Lm5 v k a5 ∧
    Fm.Ob y a ∧ ∀ p q r sp ssp oqr P opq, Fm.Ob p a5 → Fm.Ob q a5 → Fm.Ob r a5 →
      Fm.IsSg a4 a5 p sp → Fm.IsSg a3 a4 sp ssp → Fm.IsOp a3 a4 a5 q r oqr →
      Fm.IsOp a1 a2 a3 ssp oqr P → Fm.IsOp a3 a4 a5 p q opq →
      (Fm.El P y (H.op a a1) ↔ Fm.El opq c1 (H.op a2 a3))

/-- The selection condition of the symbol `VC`. -/
def T7 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 a2 a3, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lm2 v k a2 ∧ H.Lm3 v k a3 ∧
    Fm.Ob y a ∧ ∀ p, Fm.Ob p a1 → (Fm.El p y (H.op a a1) ↔
      ∃ q r, Fm.Ob q a3 ∧ Fm.Ob r a3 ∧ Fm.IsOp a1 a2 a3 q r p ∧ Fm.El r c1 (H.op a2 a3))

/-- The selection condition of the symbol `TL`. -/
def T8 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 u1 u2 u3, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lp1 v k u1 ∧ H.Lp2 v k u2 ∧ H.Lp3 v k u3 ∧
    Fm.Ob y a ∧ ∀ p, Fm.Ob p a1 → (Fm.El p y (H.op a a1) ↔
      ∀ q sp P, Fm.Ob q a → Fm.IsSg a a1 p sp → Fm.IsOp u2 u1 a q sp P → Fm.El P c1 (H.op u3 u2))

/-- The selection condition of the symbol `CV`. -/
def T9 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 a2 a3, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lm2 v k a2 ∧ H.Lm3 v k a3 ∧
    Fm.Ob y a ∧ ∀ p q r r', Fm.Ob p a3 → Fm.Ob q a3 → Fm.IsOp a1 a2 a3 p q r →
      Fm.IsOp a1 a2 a3 q p r' → (Fm.El r y (H.op a a1) ↔ Fm.El r' c1 (H.op a a1))

/-- The selection condition of the symbol `C1`. -/
def T10 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 a2, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lm2 v k a2 ∧
    Fm.Ob y a ∧ ∀ p, Fm.Ob p a1 → (Fm.El p y (H.op a a1) ↔ ∃ q, Fm.Ob q a2 ∧ Fm.IsSg a1 a2 q p)

/-- The selection condition of the symbol `SB`. -/
def T11 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 a2 a3 a4, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lm2 v k a2 ∧ H.Lm3 v k a3 ∧ H.Lm4 v k a4 ∧
    Fm.Ob y a ∧ ∀ p q o, Fm.Ob p a3 → Fm.Ob q a3 → Fm.IsOp a1 a2 a3 p q o →
      (Fm.El o y (H.op a a1) ↔ ∀ r, Fm.Ob r a4 → Fm.El r p (H.op a3 a4) → Fm.El r q (H.op a3 a4))

/-- The selection condition of the symbol `D`. -/
def T12 (y c1 c2 k v : H.W) : Prop :=
  ∃ a u1, H.L0 v k a ∧ H.Lp1 v k u1 ∧
    Fm.Ob y a ∧ ¬ (Fm.El y c1 (H.op u1 a) ↔ Fm.El y c2 (H.op u1 a))

/-- The selection condition of the symbol `P1`. -/
def T13 (y c1 c2 k v : H.W) : Prop :=
  ∃ a u1 u2, H.L0 v k a ∧ H.Lp1 v k u1 ∧ H.Lp2 v k u2 ∧
    Fm.Ob y a ∧ ∃ r, Fm.Ob r a ∧ Fm.IsOp u2 u1 a y r c1

/-- The selection condition of the symbol `P2`. -/
def T14 (y c1 c2 k v : H.W) : Prop :=
  ∃ a u1 u2, H.L0 v k a ∧ H.Lp1 v k u1 ∧ H.Lp2 v k u2 ∧
    Fm.Ob y a ∧ ∃ q, Fm.Ob q a ∧ Fm.IsOp u2 u1 a q y c1

/-- The selection condition of the symbol `EL`. -/
def T15 (y c1 c2 k v : H.W) : Prop :=
  ∃ a u1, H.L0 v k a ∧ H.Lp1 v k u1 ∧
    Fm.Ob y a ∧ Fm.IsSg u1 a y c1

/-- The selection condition of the symbol `WT`. -/
def T16 (y c1 c2 k v : H.W) : Prop :=
  ∃ a a1 u1 u2 u3, H.L0 v k a ∧ H.Lm1 v k a1 ∧ H.Lp1 v k u1 ∧ H.Lp2 v k u2 ∧ H.Lp3 v k u3 ∧
    Fm.Ob y a ∧ ∃ sp P, Fm.IsSg a a1 c1 sp ∧ Fm.IsOp u2 u1 a y sp P ∧ ¬ Fm.El P c2 (H.op u3 u2)

/-- The selection condition of the symbol `WS`. -/
def T17 (y c1 c2 k v : H.W) : Prop :=
  ∃ a u1, H.L0 v k a ∧ H.Lp1 v k u1 ∧
    Fm.Ob y a ∧ Fm.El y c1 (H.op u1 a) ∧ ¬ Fm.El y c2 (H.op u1 a)

end FlatM

/-! ## Phase 2 (A2–A4): decoding of terms, offsets, and the value of a term at a position -/

namespace Host

/-- The position at the offset with the code `o` from `k`: codes `0` (same), `1`, `2` (one,
two below), `3`, `4`, `5` (one, two, three above). -/
def Sh (H : Host) : ℕ → H.W → H.W → Prop
  | 0, k, k1 => k1 = k
  | 1, k, k1 => k = H.suc k1
  | 2, k, k1 => k = H.suc (H.suc k1)
  | 3, k, k1 => k1 = H.suc k
  | 4, k, k1 => k1 = H.suc (H.suc k)
  | 5, k, k1 => k1 = H.suc (H.suc (H.suc k))
  | _, _, _ => False

theorem sh_fun {H : Host} : ∀ (o : ℕ) {k k1 k1' : H.W}, H.Sh o k k1 → H.Sh o k k1' → k1 = k1'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | 1, _, _, _, h, h' => H.suc_inj (h.symm.trans h')
  | 2, _, _, _, h, h' => H.suc_inj (H.suc_inj (h.symm.trans h'))
  | 3, _, _, _, h, h' => h.trans h'.symm
  | 4, _, _, _, h, h' => h.trans h'.symm
  | 5, _, _, _, h, h' => h.trans h'.symm
  | (_ + 6), _, _, _, h, _ => h.elim

end Host

/-- The code of the offset of the first argument of the symbol with the tag `i`. -/
def off1 : ℕ → ℕ
  | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 5 | 9 => 0 | 10 => 0 | 11 => 0 | 12 => 3 | 13 => 4 | 14 => 4 | 15 => 3 | 16 => 1 | 17 => 3 | _ => 0

/-- The code of the offset of the second argument of the symbol with the tag `i`. -/
def off2 : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | 10 => 0 | 11 => 0 | 12 => 3 | 13 => 0 | 14 => 0 | 15 => 0 | 16 => 5 | 17 => 3 | _ => 0

namespace FlatM

variable {H : Host} (Fm : FlatM H)
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N}

/-- The tag of a symbol as a number of the host. -/
def tg (num : N → H.W) (i : ℕ) : H.W := num ((i : ℕ) : N)

/-- The selection condition of the symbol with the tag `i`. -/
def Tn : ℕ → H.W → H.W → H.W → H.W → H.W → Prop
  | 0 => Fm.T0
  | 1 => Fm.T1
  | 2 => Fm.T2
  | 3 => Fm.T3
  | 4 => Fm.T4
  | 5 => Fm.T5
  | 6 => Fm.T6
  | 7 => Fm.T7
  | 8 => Fm.T8
  | 9 => Fm.T9
  | 10 => Fm.T10
  | 11 => Fm.T11
  | 12 => Fm.T12
  | 13 => Fm.T13
  | 14 => Fm.T14
  | 15 => Fm.T15
  | 16 => Fm.T16
  | 17 => Fm.T17
  | _ => fun _ _ _ _ _ => False

/-- The position of the first argument of a term with the tag `f`. -/
def Off1 (num : N → H.W) (f k k1 : H.W) : Prop :=
    (f = tg num 0 ∧ k = H.suc k1) ∨
    (f = tg num 1 ∧ k = H.suc k1) ∨
    (f = tg num 2 ∧ k1 = k) ∨
    (f = tg num 3 ∧ k1 = k) ∨
    (f = tg num 4 ∧ k = H.suc k1) ∨
    (f = tg num 5 ∧ k = H.suc (H.suc k1)) ∨
    (f = tg num 6 ∧ k = H.suc (H.suc k1)) ∨
    (f = tg num 7 ∧ k = H.suc (H.suc k1)) ∨
    (f = tg num 8 ∧ k1 = H.suc (H.suc (H.suc k))) ∨
    (f = tg num 9 ∧ k1 = k) ∨
    (f = tg num 10 ∧ k1 = k) ∨
    (f = tg num 11 ∧ k1 = k) ∨
    (f = tg num 12 ∧ k1 = H.suc k) ∨
    (f = tg num 13 ∧ k1 = H.suc (H.suc k)) ∨
    (f = tg num 14 ∧ k1 = H.suc (H.suc k)) ∨
    (f = tg num 15 ∧ k1 = H.suc k) ∨
    (f = tg num 16 ∧ k = H.suc k1) ∨
    (f = tg num 17 ∧ k1 = H.suc k)

/-- The position of the second argument of a term with the tag `f`. -/
def Off2 (num : N → H.W) (f k k2 : H.W) : Prop :=
    (f = tg num 0 ∧ k2 = k) ∨
    (f = tg num 1 ∧ k = H.suc k2) ∨
    (f = tg num 2 ∧ k2 = k) ∨
    (f = tg num 3 ∧ k2 = k) ∨
    (f = tg num 4 ∧ k2 = k) ∨
    (f = tg num 5 ∧ k2 = k) ∨
    (f = tg num 6 ∧ k2 = k) ∨
    (f = tg num 7 ∧ k2 = k) ∨
    (f = tg num 8 ∧ k2 = k) ∨
    (f = tg num 9 ∧ k2 = k) ∨
    (f = tg num 10 ∧ k2 = k) ∨
    (f = tg num 11 ∧ k2 = k) ∨
    (f = tg num 12 ∧ k2 = H.suc k) ∨
    (f = tg num 13 ∧ k2 = k) ∨
    (f = tg num 14 ∧ k2 = k) ∨
    (f = tg num 15 ∧ k2 = k) ∨
    (f = tg num 16 ∧ k2 = H.suc (H.suc (H.suc k))) ∨
    (f = tg num 17 ∧ k2 = H.suc k)

/-- The selection condition for the tag `f`; `p` is `((c1, c2), (k, v))`. -/
def Th (num : N → H.W) (f y p : H.W) : Prop :=
  ∃ c1 c2 k v, p = H.op (H.op c1 c2) (H.op k v) ∧
    ((f = tg num 0 ∧ Fm.T0 y c1 c2 k v) ∨
    (f = tg num 1 ∧ Fm.T1 y c1 c2 k v) ∨
    (f = tg num 2 ∧ Fm.T2 y c1 c2 k v) ∨
    (f = tg num 3 ∧ Fm.T3 y c1 c2 k v) ∨
    (f = tg num 4 ∧ Fm.T4 y c1 c2 k v) ∨
    (f = tg num 5 ∧ Fm.T5 y c1 c2 k v) ∨
    (f = tg num 6 ∧ Fm.T6 y c1 c2 k v) ∨
    (f = tg num 7 ∧ Fm.T7 y c1 c2 k v) ∨
    (f = tg num 8 ∧ Fm.T8 y c1 c2 k v) ∨
    (f = tg num 9 ∧ Fm.T9 y c1 c2 k v) ∨
    (f = tg num 10 ∧ Fm.T10 y c1 c2 k v) ∨
    (f = tg num 11 ∧ Fm.T11 y c1 c2 k v) ∨
    (f = tg num 12 ∧ Fm.T12 y c1 c2 k v) ∨
    (f = tg num 13 ∧ Fm.T13 y c1 c2 k v) ∨
    (f = tg num 14 ∧ Fm.T14 y c1 c2 k v) ∨
    (f = tg num 15 ∧ Fm.T15 y c1 c2 k v) ∨
    (f = tg num 16 ∧ Fm.T16 y c1 c2 k v) ∨
    (f = tg num 17 ∧ Fm.T17 y c1 c2 k v))

theorem off1_iff (num : N → H.W) {f k k1 : H.W} :
    Off1 num f k k1 ↔ ∃ i, i < 18 ∧ f = tg num i ∧ H.Sh (off1 i) k k1 := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨0, by decide, h1, h2⟩
    · exact ⟨1, by decide, h1, h2⟩
    · exact ⟨2, by decide, h1, h2⟩
    · exact ⟨3, by decide, h1, h2⟩
    · exact ⟨4, by decide, h1, h2⟩
    · exact ⟨5, by decide, h1, h2⟩
    · exact ⟨6, by decide, h1, h2⟩
    · exact ⟨7, by decide, h1, h2⟩
    · exact ⟨8, by decide, h1, h2⟩
    · exact ⟨9, by decide, h1, h2⟩
    · exact ⟨10, by decide, h1, h2⟩
    · exact ⟨11, by decide, h1, h2⟩
    · exact ⟨12, by decide, h1, h2⟩
    · exact ⟨13, by decide, h1, h2⟩
    · exact ⟨14, by decide, h1, h2⟩
    · exact ⟨15, by decide, h1, h2⟩
    · exact ⟨16, by decide, h1, h2⟩
    · exact ⟨17, by decide, h1, h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    interval_cases i
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h1, h2⟩)))))))))))))))))

theorem off2_iff (num : N → H.W) {f k k2 : H.W} :
    Off2 num f k k2 ↔ ∃ i, i < 18 ∧ f = tg num i ∧ H.Sh (off2 i) k k2 := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨0, by decide, h1, h2⟩
    · exact ⟨1, by decide, h1, h2⟩
    · exact ⟨2, by decide, h1, h2⟩
    · exact ⟨3, by decide, h1, h2⟩
    · exact ⟨4, by decide, h1, h2⟩
    · exact ⟨5, by decide, h1, h2⟩
    · exact ⟨6, by decide, h1, h2⟩
    · exact ⟨7, by decide, h1, h2⟩
    · exact ⟨8, by decide, h1, h2⟩
    · exact ⟨9, by decide, h1, h2⟩
    · exact ⟨10, by decide, h1, h2⟩
    · exact ⟨11, by decide, h1, h2⟩
    · exact ⟨12, by decide, h1, h2⟩
    · exact ⟨13, by decide, h1, h2⟩
    · exact ⟨14, by decide, h1, h2⟩
    · exact ⟨15, by decide, h1, h2⟩
    · exact ⟨16, by decide, h1, h2⟩
    · exact ⟨17, by decide, h1, h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    interval_cases i
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h1, h2⟩)))))))))))))))))

theorem th_iff (num : N → H.W) {f y c1 c2 k v : H.W} :
    Fm.Th num f y (H.op (H.op c1 c2) (H.op k v)) ↔
      ∃ i, i < 18 ∧ f = tg num i ∧ Fm.Tn i y c1 c2 k v := by
  constructor
  · rintro ⟨c1', c2', k', v', e, h⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    obtain ⟨e3, e4⟩ := H.op_inj e1
    obtain ⟨e5, e6⟩ := H.op_inj e2
    subst e3 e4 e5 e6
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, by decide, h1, h2⟩
    · exact ⟨1, by decide, h1, h2⟩
    · exact ⟨2, by decide, h1, h2⟩
    · exact ⟨3, by decide, h1, h2⟩
    · exact ⟨4, by decide, h1, h2⟩
    · exact ⟨5, by decide, h1, h2⟩
    · exact ⟨6, by decide, h1, h2⟩
    · exact ⟨7, by decide, h1, h2⟩
    · exact ⟨8, by decide, h1, h2⟩
    · exact ⟨9, by decide, h1, h2⟩
    · exact ⟨10, by decide, h1, h2⟩
    · exact ⟨11, by decide, h1, h2⟩
    · exact ⟨12, by decide, h1, h2⟩
    · exact ⟨13, by decide, h1, h2⟩
    · exact ⟨14, by decide, h1, h2⟩
    · exact ⟨15, by decide, h1, h2⟩
    · exact ⟨16, by decide, h1, h2⟩
    · exact ⟨17, by decide, h1, h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    refine ⟨c1, c2, k, v, rfl, ?_⟩
    interval_cases i
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h1, h2⟩)))))))))))))))))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem def_th (num : N → H.W) : Def3 H (Fm.Th num) := by
  have h1 := Fm.defOb
  have h2 := Fm.defEl
  hdef

end FlatM

/-! ## Phase 2 (A4): the value of a term at a position of a placement -/

namespace Host

variable {H : Host}

namespace Arith

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}
variable (ar : H.Arith E num)

/-- The graph of the pairing function on the numbers of the host. -/
def Pr (x y z : H.W) : Prop := ∃ s t, ar.Ad x y s ∧ ar.Mu s s t ∧ ar.Ad t x z

theorem pr_iff {x y : N} {z : H.W} : ar.Pr (num x) (num y) z ↔ z = num (npair x y) := by
  constructor
  · rintro ⟨s, t, h1, h2, h3⟩
    rw [ar.ad_iff.mp h1] at h2
    rw [ar.mu_iff.mp h2] at h3
    exact ar.ad_iff.mp h3
  · rintro rfl
    exact ⟨_, _, ar.ad_iff.mpr rfl, ar.mu_iff.mpr rfl, ar.ad_iff.mpr rfl⟩

/-- `n` is the code of the term with the tag `f` and the arguments `n1`, `n2`. -/
def Dec (n f n1 n2 : H.W) : Prop :=
  f ∈ H.om ∧ n1 ∈ H.om ∧ n2 ∈ H.om ∧ ∃ p q, ar.Pr n1 n2 p ∧ ar.Pr f p q ∧ n = H.suc q

theorem dec_iff {n f n1 n2 : H.W} : ar.Dec n f n1 n2 ↔ ∃ f' x y : N, f = num f' ∧ n1 = num x ∧
    n2 = num y ∧ n = num (npair f' (npair x y) + 1) := by
  constructor
  · rintro ⟨hf, h1, h2, p, q, hp, hq, hn⟩
    obtain ⟨f', rfl⟩ := ar.of_om hf
    obtain ⟨x, rfl⟩ := ar.of_om h1
    obtain ⟨y, rfl⟩ := ar.of_om h2
    rw [ar.pr_iff.mp hp] at hq
    rw [ar.pr_iff.mp hq, ← ar.iso.succ] at hn
    exact ⟨f', x, y, rfl, rfl, rfl, hn⟩
  · rintro ⟨f', x, y, rfl, rfl, rfl, rfl⟩
    exact ⟨ar.num_om _, ar.num_om _, ar.num_om _, _, _, ar.pr_iff.mpr rfl, ar.pr_iff.mpr rfl,
      ar.iso.succ _⟩

theorem dec_unique {n f n1 n2 f' n1' n2' : H.W} (h : ar.Dec n f n1 n2)
    (h' : ar.Dec n f' n1' n2') : f = f' ∧ n1 = n1' ∧ n2 = n2' := by
  obtain ⟨a, x, y, rfl, rfl, rfl, rfl⟩ := ar.dec_iff.mp h
  obtain ⟨a', x', y', rfl, rfl, rfl, e⟩ := ar.dec_iff.mp h'
  have e1 := ar.nf.succ_inj (ar.num_inj e)
  obtain ⟨e2, e3⟩ := ar.nf.pair_inj _ _ _ _ e1
  obtain ⟨e4, e5⟩ := ar.nf.pair_inj _ _ _ _ e3
  rw [e2, e4, e5]
  exact ⟨rfl, rfl, rfl⟩

include ar in
theorem le_npair_left (x y : N) : x ≤ npair x y :=
  (ar.nf.le_iff _ _).mpr ⟨(x + y) * (x + y), by unfold npair; ring⟩

include ar in
theorem le_npair_right (x y : N) : y ≤ npair x y := by
  have h1 : y ≤ x + y := (ar.nf.le_iff _ _).mpr ⟨x, add_comm y x⟩
  have h2 : x + y ≤ npair x y := le_trans (ar.nf.le_mul_self (x + y)) (ar.nf.le_add _ x)
  exact le_trans h1 h2

theorem dec_tm (f : ℕ) (x y : N) : ar.Dec (num (tm f x y)) (num ((f : ℕ) : N)) (num x) (num y) :=
  ar.dec_iff.mpr ⟨_, x, y, rfl, rfl, rfl, rfl⟩

/-- The arguments of a term have smaller codes. -/
theorem dec_mem {n f n1 n2 : H.W} (h : ar.Dec n f n1 n2) : n1 ∈ n ∧ n2 ∈ n := by
  obtain ⟨a, x, y, rfl, rfl, rfl, rfl⟩ := ar.dec_iff.mp h
  have h1 := ar.le_npair_right a (npair x y)
  exact ⟨ar.num_mem.mpr (ar.nf.add_le_add_r (le_trans (ar.le_npair_left x y) h1) 1),
    ar.num_mem.mpr (ar.nf.add_le_add_r (le_trans (ar.le_npair_right x y) h1) 1)⟩

end Arith

end Host

namespace FlatM

variable {H : Host} (Fm : FlatM H)
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

theorem tg_inj (ar : H.Arith E num) {i j : ℕ} (h : tg num i = tg num j) : i = j :=
  ar.nf.cast_inj i j (ar.num_inj h)

/-- `c` is the least object of the level `a`. -/
def Least (a c : H.W) : Prop := Fm.Ob c a ∧ ∀ y, H.lt y c → ¬ Fm.Ob y a

/-- The object selected: the least `c` that satisfies the selection condition, or the least
object of the level if nothing satisfies it. -/
def Pick (num : N → H.W) (f a c p : H.W) : Prop :=
  (Fm.Th num f c p ∧ ∀ y, H.lt y c → ¬ Fm.Th num f y p) ∨
    ((¬ ∃ y, Fm.Th num f y p) ∧ Fm.Least a c)

/-- `n` is a term with the tag `f` and the arguments `n1`, `n2`, whose positions `k1`, `k2`
relative to `k` are positions of the placement `v`. -/
def Args (ar : H.Arith E num) (v n k f n1 n2 k1 k2 : H.W) : Prop :=
  ar.Dec n f n1 n2 ∧ Off1 num f k k1 ∧ Off2 num f k k2 ∧ (∃ b, H.App v k1 b) ∧ ∃ b, H.App v k2 b

/-- The clause of the recursion, with a set `D` of triples in place of the value relation. -/
def Cl (ar : H.Arith E num) (D v n k c : H.W) : Prop :=
  ∃ a, H.App v k a ∧
    ((∃ f n1 n2 k1 k2 c1 c2, Args ar v n k f n1 n2 k1 k2 ∧ H.op n1 (H.op k1 c1) ∈ D ∧
        H.op n2 (H.op k2 c2) ∈ D ∧ Fm.Pick num f a c (H.op (H.op c1 c2) (H.op k v))) ∨
      ((¬ ∃ f n1 n2 k1 k2, Args ar v n k f n1 n2 k1 k2) ∧ Fm.Least a c))

/-- Every member of `D` satisfies the clause relative to `D`. -/
def SelfSup (ar : H.Arith E num) (D v : H.W) : Prop :=
  ∀ n k c, H.op n (H.op k c) ∈ D → Fm.Cl ar D v n k c

/-- The value relation; `p` is the pair of the position and the placement. -/
def Vl (ar : H.Arith E num) (n c p : H.W) : Prop :=
  ∃ k v D, p = H.op k v ∧ Fm.SelfSup ar D v ∧ H.op n (H.op k c) ∈ D

/-- `c` is the value of the term `n` at the position `k` of the placement `v`. -/
def Val (ar : H.Arith E num) (n k v c : H.W) : Prop := Fm.Vl ar n c (H.op k v)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem def_vl (ar : H.Arith E num) : Def3 H (Fm.Vl ar) := by
  have h1 := Fm.defOb
  have h2 := Fm.def_th num
  have h3 := ar.def_Ad
  have h4 := ar.def_Mu
  hdef

theorem val_def (ar : H.Arith E num) {n k v c : H.W} :
    Fm.Val ar n k v c ↔ ∃ D, Fm.SelfSup ar D v ∧ H.op n (H.op k c) ∈ D := by
  constructor
  · rintro ⟨k', v', D, e, h1, h2⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    subst e1 e2
    exact ⟨D, h1, h2⟩
  · rintro ⟨D, h1, h2⟩
    exact ⟨k, v, D, rfl, h1, h2⟩

theorem cl_mono (ar : H.Arith E num) {D D' v n k c : H.W} (hs : H.Sub D D')
    (h : Fm.Cl ar D v n k c) : Fm.Cl ar D' v n k c := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ha, ?_⟩
  rcases h with ⟨f, n1, n2, k1, k2, c1, c2, h1, h2, h3, h4⟩ | h
  · exact Or.inl ⟨f, n1, n2, k1, k2, c1, c2, h1, hs _ h2, hs _ h3, h4⟩
  · exact Or.inr h

/-- **The recursion equation of the value relation.** -/
theorem val_iff (ar : H.Arith E num) {n k v c : H.W} : Fm.Val ar n k v c ↔
    ∃ a, H.App v k a ∧
      ((∃ f n1 n2 k1 k2 c1 c2, Args ar v n k f n1 n2 k1 k2 ∧ Fm.Val ar n1 k1 v c1 ∧
          Fm.Val ar n2 k2 v c2 ∧ Fm.Pick num f a c (H.op (H.op c1 c2) (H.op k v))) ∨
        ((¬ ∃ f n1 n2 k1 k2, Args ar v n k f n1 n2 k1 k2) ∧ Fm.Least a c)) := by
  rw [Fm.val_def ar]
  constructor
  · rintro ⟨D, hD, hm⟩
    obtain ⟨a, ha, h⟩ := hD n k c hm
    refine ⟨a, ha, ?_⟩
    rcases h with ⟨f, n1, n2, k1, k2, c1, c2, h1, h2, h3, h4⟩ | h
    · exact Or.inl ⟨f, n1, n2, k1, k2, c1, c2, h1, (Fm.val_def ar).mpr ⟨D, hD, h2⟩,
        (Fm.val_def ar).mpr ⟨D, hD, h3⟩, h4⟩
    · exact Or.inr h
  · rintro ⟨a, ha, h⟩
    rcases h with ⟨f, n1, n2, k1, k2, c1, c2, h1, h2, h3, h4⟩ | h
    · obtain ⟨D1, hD1, hm1⟩ := (Fm.val_def ar).mp h2
      obtain ⟨D2, hD2, hm2⟩ := (Fm.val_def ar).mp h3
      have s1 : H.Sub D1 (H.bun (H.bun D1 D2) (H.sg (H.op n (H.op k c)))) :=
        fun z hz => H.mem_bun.mpr (Or.inl (H.mem_bun.mpr (Or.inl hz)))
      have s2 : H.Sub D2 (H.bun (H.bun D1 D2) (H.sg (H.op n (H.op k c)))) :=
        fun z hz => H.mem_bun.mpr (Or.inl (H.mem_bun.mpr (Or.inr hz)))
      refine ⟨H.bun (H.bun D1 D2) (H.sg (H.op n (H.op k c))), fun m j e hm => ?_,
        H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl))⟩
      rcases H.mem_bun.mp hm with hm' | hm'
      · rcases H.mem_bun.mp hm' with hm'' | hm''
        · exact Fm.cl_mono ar s1 (hD1 m j e hm'')
        · exact Fm.cl_mono ar s2 (hD2 m j e hm'')
      · obtain ⟨e1, e2⟩ := H.op_inj (H.mem_sg.mp hm')
        obtain ⟨e3, e4⟩ := H.op_inj e2
        subst e1 e3 e4
        exact ⟨a, ha, Or.inl ⟨f, n1, n2, k1, k2, c1, c2, h1, s1 _ hm1, s2 _ hm2, h4⟩⟩
    · refine ⟨H.sg (H.op n (H.op k c)), fun m j e hm => ?_, H.mem_sg.mpr rfl⟩
      obtain ⟨e1, e2⟩ := H.op_inj (H.mem_sg.mp hm)
      obtain ⟨e3, e4⟩ := H.op_inj e2
      subst e1 e3 e4
      exact ⟨a, ha, Or.inr h⟩

variable {Fm}

theorem least_unique {a c c' : H.W} (h : Fm.Least a c) (h' : Fm.Least a c') : c = c' := by
  rcases H.lt_tri c c' with h1 | h1 | h1
  · exact (h'.2 c h1 h.1).elim
  · exact h1
  · exact (h.2 c' h1 h'.1).elim

theorem pick_unique {f a c c' p : H.W} (h : Fm.Pick num f a c p) (h' : Fm.Pick num f a c' p) :
    c = c' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h' with ⟨h1', h2'⟩ | ⟨h1', -⟩
    · rcases H.lt_tri c c' with h3 | h3 | h3
      · exact (h2' c h3 h1).elim
      · exact h3
      · exact (h2 c' h3 h1').elim
    · exact (h1' ⟨c, h1⟩).elim
  · rcases h' with ⟨h1', -⟩ | ⟨-, h2'⟩
    · exact (h1 ⟨c', h1'⟩).elim
    · exact least_unique h2 h2'

theorem args_unique (ar : H.Arith E num) {v n k f n1 n2 k1 k2 f' n1' n2' k1' k2' : H.W}
    (h : Args ar v n k f n1 n2 k1 k2) (h' : Args ar v n k f' n1' n2' k1' k2') :
    f = f' ∧ n1 = n1' ∧ n2 = n2' ∧ k1 = k1' ∧ k2 = k2' := by
  obtain ⟨e1, e2, e3⟩ := ar.dec_unique h.1 h'.1
  subst e1 e2 e3
  obtain ⟨i, -, hi, hs⟩ := (off1_iff num).mp h.2.1
  obtain ⟨i', -, hi', hs'⟩ := (off1_iff num).mp h'.2.1
  have ei := tg_inj ar (hi.symm.trans hi')
  subst ei
  obtain ⟨j, -, hj, ht⟩ := (off2_iff num).mp h.2.2.1
  obtain ⟨j', -, hj', ht'⟩ := (off2_iff num).mp h'.2.2.1
  have ej := tg_inj ar (hj.symm.trans hj')
  subst ej
  exact ⟨rfl, rfl, rfl, H.sh_fun _ hs hs', H.sh_fun _ ht ht'⟩

variable (ax : Fm.Ax)
include ax

theorem least_ex {a : H.W} (ha : Fm.Lv a) : ∃ c, Fm.Least a c := by
  have h1 := Fm.defOb
  obtain ⟨x, hx⟩ := ax.ne a ha
  obtain ⟨c, hc, hmin⟩ := H.least' (fun y => Fm.Ob y a) (by hdef) hx
  exact ⟨c, hc, hmin⟩

theorem pick_ex (num : N → H.W) (f p : H.W) {a : H.W} (ha : Fm.Lv a) :
    ∃ c, Fm.Pick num f a c p := by
  have h2 := Fm.def_th num
  by_cases h : ∃ y, Fm.Th num f y p
  · obtain ⟨y, hy⟩ := h
    obtain ⟨c, hc, hmin⟩ := H.least' (fun y => Fm.Th num f y p) (by hdef) hy
    exact ⟨c, Or.inl ⟨hc, hmin⟩⟩
  · obtain ⟨c, hc⟩ := FlatM.least_ex ax ha
    exact ⟨c, Or.inr ⟨h, hc⟩⟩

/-- Every term has a value at every position of a placement into the levels. -/
theorem val_tot (ar : H.Arith E num) {v : H.W} (hv : ∀ k a, H.App v k a → Fm.Lv a) :
    ∀ n k a, H.App v k a → ∃ c, Fm.Val ar n k v c := by
  have hV := Fm.def_vl ar
  refine H.lt_ind (fun n => ∀ k a, H.App v k a → ∃ c, Fm.Val ar n k v c) (by hdef) ?_
  intro n ih k a ha
  by_cases hargs : ∃ f n1 n2 k1 k2, Args ar v n k f n1 n2 k1 k2
  · obtain ⟨f, n1, n2, k1, k2, h⟩ := hargs
    obtain ⟨hn1, hn2⟩ := ar.dec_mem h.1
    obtain ⟨b1, hb1⟩ := h.2.2.2.1
    obtain ⟨b2, hb2⟩ := h.2.2.2.2
    obtain ⟨c1, hc1⟩ := ih n1 (H.mem_lt _ _ hn1) k1 b1 hb1
    obtain ⟨c2, hc2⟩ := ih n2 (H.mem_lt _ _ hn2) k2 b2 hb2
    obtain ⟨c, hc⟩ := FlatM.pick_ex ax num f (H.op (H.op c1 c2) (H.op k v)) (hv k a ha)
    exact ⟨c, (Fm.val_iff ar).mpr ⟨a, ha, Or.inl ⟨f, n1, n2, k1, k2, c1, c2, h, hc1, hc2, hc⟩⟩⟩
  · obtain ⟨c, hc⟩ := FlatM.least_ex ax (hv k a ha)
    exact ⟨c, (Fm.val_iff ar).mpr ⟨a, ha, Or.inr ⟨hargs, hc⟩⟩⟩

omit ax in
/-- The value of a term at a position is unique. -/
theorem val_fun (ar : H.Arith E num) {v : H.W} (hvf : H.IsFun v) :
    ∀ n k c c', Fm.Val ar n k v c → Fm.Val ar n k v c' → c = c' := by
  have hV := Fm.def_vl ar
  refine H.lt_ind (fun n => ∀ k c c', Fm.Val ar n k v c → Fm.Val ar n k v c' → c = c')
    (by hdef) ?_
  intro n ih k c c' h h'
  obtain ⟨a, ha, h⟩ := (Fm.val_iff ar).mp h
  obtain ⟨a', ha', h'⟩ := (Fm.val_iff ar).mp h'
  have ea := hvf.2 _ _ _ ha ha'
  subst ea
  rcases h with ⟨f, n1, n2, k1, k2, c1, c2, h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · rcases h' with ⟨f', n1', n2', k1', k2', c1', c2', h1', h2', h3', h4'⟩ | ⟨h1', -⟩
    · obtain ⟨e1, e2, e3, e4, e5⟩ := args_unique ar h1 h1'
      subst e1 e2 e3 e4 e5
      obtain ⟨hn1, hn2⟩ := ar.dec_mem h1.1
      have ec1 := ih n1 (H.mem_lt _ _ hn1) k1 c1 c1' h2 h2'
      have ec2 := ih n2 (H.mem_lt _ _ hn2) k2 c2 c2' h3 h3'
      subst ec1 ec2
      exact pick_unique h4 h4'
    · exact (h1' ⟨f, n1, n2, k1, k2, h1⟩).elim
  · rcases h' with ⟨f', n1', n2', k1', k2', c1', c2', h1', -⟩ | ⟨-, h2'⟩
    · exact (h1 ⟨f', n1', n2', k1', k2', h1'⟩).elim
    · exact least_unique h2 h2'

end FlatM

/-! ## Phase 2 (A5, generated): the selection conditions with explicit levels, and the value
of each symbol

Generated by `gen/gen46.py`. For the symbol with the tag `i`, `ti_iff` rewrites the selection
condition at the position `suc^D k0` in terms of the levels `lvl v (suc^m k0)`, and `vali_spec`
says that the value of a term with this symbol satisfies the condition if anything does. -/

namespace Host

/-- The level at the position `j` of the placement `v`. -/
noncomputable def lvl (H : Host) (v j : H.W) : H.W :=
  open Classical in if h : ∃ a, H.App v j a then Classical.choose h else j

theorem lvl_spec {H : Host} {v j : H.W} (h : ∃ b, H.App v j b) : H.App v j (H.lvl v j) := by
  unfold lvl
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem lvl_eq {H : Host} {v j a : H.W} (hvf : H.IsFun v) (h : H.App v j a) : a = H.lvl v j :=
  hvf.2 _ _ _ h (H.lvl_spec ⟨a, h⟩)

theorem lm1_suc {H : Host} {v k a : H.W} : H.Lm1 v (H.suc k) a ↔ H.App v k a :=
  ⟨fun ⟨k1, e, h⟩ => by rw [H.suc_inj e]; exact h, fun h => ⟨k, rfl, h⟩⟩

theorem lm2_suc {H : Host} {v k a : H.W} : H.Lm2 v (H.suc k) a ↔ H.Lm1 v k a :=
  ⟨fun ⟨k1, e, h⟩ => by rw [H.suc_inj e]; exact h, fun h => ⟨k, rfl, h⟩⟩

theorem lm3_suc {H : Host} {v k a : H.W} : H.Lm3 v (H.suc k) a ↔ H.Lm2 v k a :=
  ⟨fun ⟨k1, e, h⟩ => by rw [H.suc_inj e]; exact h, fun h => ⟨k, rfl, h⟩⟩

theorem lm4_suc {H : Host} {v k a : H.W} : H.Lm4 v (H.suc k) a ↔ H.Lm3 v k a :=
  ⟨fun ⟨k1, e, h⟩ => by rw [H.suc_inj e]; exact h, fun h => ⟨k, rfl, h⟩⟩

theorem lm5_suc {H : Host} {v k a : H.W} : H.Lm5 v (H.suc k) a ↔ H.Lm4 v k a :=
  ⟨fun ⟨k1, e, h⟩ => by rw [H.suc_inj e]; exact h, fun h => ⟨k, rfl, h⟩⟩

end Host

/-- A placement: an increasing sequence of levels. -/
structure FlatM.Plc {H : Host} (Fm : FlatM H) (v : H.W) : Prop where
  seq : ∃ L, H.IncSeq v L
  lv : ∀ k a, H.App v k a → Fm.Lv a

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

theorem Plc.fn {v : H.W} (hv : Fm.Plc v) : H.IsFun v := by
  obtain ⟨L, hL⟩ := hv.seq
  exact hL.1.1

theorem plc_lt {v j : H.W} (hv : Fm.Plc v) (h0 : ∃ b, H.App v j b) (h1 : ∃ b, H.App v (H.suc j) b) :
    Fm.Lt (H.lvl v j) (H.lvl v (H.suc j)) := by
  obtain ⟨L, hL⟩ := hv.seq
  have a0 := H.lvl_spec h0
  have a1 := H.lvl_spec h1
  exact ⟨hv.lv _ _ a1, hL.2.2.2 _ _ _ _ a0 a1 (H.mem_suc.mpr (Or.inr rfl)), (hv.lv _ _ a0).2⟩

/-- An object that satisfies a selection condition is an object of the level of the position. -/
theorem tn_ob : ∀ (i : ℕ) {y c1 c2 k v : H.W}, Fm.Tn i y c1 c2 k v → ∃ a, H.App v k a ∧ Fm.Ob y a
  | 0, _, _, _, _, _, ⟨a, _, h0, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 1, _, _, _, _, _, ⟨a, _, h0, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 2, _, _, _, _, _, ⟨a, _, h0, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 3, _, _, _, _, _, ⟨a, _, h0, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 4, _, _, _, _, _, ⟨a, _, _, _, _, h0, _, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 5, _, _, _, _, _, ⟨a, _, _, _, _, _, h0, _, _, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 6, _, _, _, _, _, ⟨a, _, _, _, _, _, h0, _, _, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 7, _, _, _, _, _, ⟨a, _, _, _, h0, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 8, _, _, _, _, _, ⟨a, _, _, _, _, h0, _, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 9, _, _, _, _, _, ⟨a, _, _, _, h0, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 10, _, _, _, _, _, ⟨a, _, _, h0, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 11, _, _, _, _, _, ⟨a, _, _, _, _, h0, _, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 12, _, _, _, _, _, ⟨a, _, h0, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 13, _, _, _, _, _, ⟨a, _, _, h0, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 14, _, _, _, _, _, ⟨a, _, _, h0, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 15, _, _, _, _, _, ⟨a, _, h0, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 16, _, _, _, _, _, ⟨a, _, _, _, _, h0, _, _, _, _, hb⟩ => ⟨a, h0, hb.1⟩
  | 17, _, _, _, _, _, ⟨a, _, h0, _, hb⟩ => ⟨a, h0, hb.1⟩
  | (_ + 18), _, _, _, _, _, h => h.elim

theorem t0_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.T0 y c1 c2 (H.suc k0) v ↔
      (Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) c1 y) := by
  constructor
  · rintro ⟨a, a1, h_a, h_a1, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp1), ((H.lm1_suc).mpr (H.lvl_spec hp0)), hb⟩

theorem t1_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.T1 y c1 c2 (H.suc k0) v ↔
      (Fm.IsUp (H.lvl v (H.suc k0)) (H.lvl v k0) c1 c2 y) := by
  constructor
  · rintro ⟨a, a1, h_a, h_a1, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp1), ((H.lm1_suc).mpr (H.lvl_spec hp0)), hb⟩

theorem t2_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.T2 y c1 c2 (H.suc k0) v ↔
      (Fm.Ob y (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z y (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      Fm.El z c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ Fm.El z c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)))) := by
  constructor
  · rintro ⟨a, a1, h_a, h_a1, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp1), ((H.lm1_suc).mpr (H.lvl_spec hp0)), hb⟩

theorem t3_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.T3 y c1 c2 (H.suc k0) v ↔
      (Fm.Ob y (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z y (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ ¬ Fm.El z c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)))) := by
  constructor
  · rintro ⟨a, a1, h_a, h_a1, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp1), ((H.lm1_suc).mpr (H.lvl_spec hp0)), hb⟩

theorem t4_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.T4 y c1 c2 (H.suc (H.suc (H.suc (H.suc k0)))) v ↔
      (Fm.Ob y (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ z w sz sw P Q, Fm.Ob z (H.lvl v k0) → Fm.Ob w (H.lvl v k0) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) z sz →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) w sw → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sz sw P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) z w Q →
      (Fm.El P y (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ Fm.El Q c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))))) := by
  constructor
  · rintro ⟨a, a1, a2, a3, a4, h_a, h_a1, h_a2, h_a3, h_a4, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp h_a2))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp h_a3)))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp ((H.lm4_suc).mp h_a4))))
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))), (H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp4), ((H.lm1_suc).mpr (H.lvl_spec hp3)), ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp2))), ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp1)))), ((H.lm4_suc).mpr ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp0))))), hb⟩

theorem t5_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b) :
    Fm.T5 y c1 c2 (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v ↔
      (Fm.Ob y (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opr, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p r opr →
      (Fm.El P y (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opr c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))))) := by
  constructor
  · rintro ⟨a, a1, a2, a3, a4, a5, h_a, h_a1, h_a2, h_a3, h_a4, h_a5, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp h_a2))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp h_a3)))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp ((H.lm4_suc).mp h_a4))))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp ((H.lm4_suc).mp ((H.lm5_suc).mp h_a5)))))
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))), (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))), (H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp5), ((H.lm1_suc).mpr (H.lvl_spec hp4)), ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp3))), ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp2)))), ((H.lm4_suc).mpr ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp1))))), ((H.lm5_suc).mpr ((H.lm4_suc).mpr ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp0)))))), hb⟩

theorem t6_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b) :
    Fm.T6 y c1 c2 (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v ↔
      (Fm.Ob y (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opq, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q opq →
      (Fm.El P y (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opq c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))))) := by
  constructor
  · rintro ⟨a, a1, a2, a3, a4, a5, h_a, h_a1, h_a2, h_a3, h_a4, h_a5, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp h_a2))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp h_a3)))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp ((H.lm4_suc).mp h_a4))))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp ((H.lm4_suc).mp ((H.lm5_suc).mp h_a5)))))
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))), (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))), (H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp5), ((H.lm1_suc).mpr (H.lvl_spec hp4)), ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp3))), ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp2)))), ((H.lm4_suc).mpr ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp1))))), ((H.lm5_suc).mpr ((H.lm4_suc).mpr ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp0)))))), hb⟩

theorem t7_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) :
    Fm.T7 y c1 c2 (H.suc (H.suc (H.suc k0))) v ↔
      (Fm.Ob y (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc (H.suc k0))) → (Fm.El p y (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔
      ∃ q r, Fm.Ob q (H.lvl v k0) ∧ Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r p ∧ Fm.El r c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)))) := by
  constructor
  · rintro ⟨a, a1, a2, a3, h_a, h_a1, h_a2, h_a3, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp h_a2))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp h_a3)))
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp3), ((H.lm1_suc).mpr (H.lvl_spec hp2)), ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp1))), ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp0)))), hb⟩

theorem t8_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.T8 y c1 c2 (H.suc k0) v ↔
      (Fm.Ob y (H.lvl v (H.suc k0)) ∧ ∀ p, Fm.Ob p (H.lvl v k0) → (Fm.El p y (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      ∀ q sp P, Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) q sp P → Fm.El P c1 (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))))) := by
  constructor
  · rintro ⟨a, a1, u1, u2, u3, h_a, h_a1, h_u1, h_u2, h_u3, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf h_u1
    obtain rfl := H.lvl_eq hvf h_u2
    obtain rfl := H.lvl_eq hvf h_u3
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))), (H.lvl_spec hp1), ((H.lm1_suc).mpr (H.lvl_spec hp0)), (H.lvl_spec hp2), (H.lvl_spec hp3), (H.lvl_spec hp4), hb⟩

theorem t9_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) :
    Fm.T9 y c1 c2 (H.suc (H.suc (H.suc k0))) v ↔
      (Fm.Ob y (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p q r r', Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q r →
      Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q p r' → (Fm.El r y (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔ Fm.El r' c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))))) := by
  constructor
  · rintro ⟨a, a1, a2, a3, h_a, h_a1, h_a2, h_a3, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp h_a2))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp h_a3)))
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp3), ((H.lm1_suc).mpr (H.lvl_spec hp2)), ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp1))), ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp0)))), hb⟩

theorem t10_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) :
    Fm.T10 y c1 c2 (H.suc (H.suc k0)) v ↔
      (Fm.Ob y (H.lvl v (H.suc (H.suc k0))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc k0)) → (Fm.El p y (H.op (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0))) ↔ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) q p)) := by
  constructor
  · rintro ⟨a, a1, a2, h_a, h_a1, h_a2, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp h_a2))
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp2), ((H.lm1_suc).mpr (H.lvl_spec hp1)), ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp0))), hb⟩

theorem t11_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.T11 y c1 c2 (H.suc (H.suc (H.suc (H.suc k0)))) v ↔
      (Fm.Ob y (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ p q o, Fm.Ob p (H.lvl v (H.suc k0)) → Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) p q o →
      (Fm.El o y (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ ∀ r, Fm.Ob r (H.lvl v k0) → Fm.El r p (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) → Fm.El r q (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)))) := by
  constructor
  · rintro ⟨a, a1, a2, a3, a4, h_a, h_a1, h_a2, h_a3, h_a4, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp h_a2))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp h_a3)))
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp ((H.lm2_suc).mp ((H.lm3_suc).mp ((H.lm4_suc).mp h_a4))))
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))), (H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl_spec hp4), ((H.lm1_suc).mpr (H.lvl_spec hp3)), ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp2))), ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp1)))), ((H.lm4_suc).mpr ((H.lm3_suc).mpr ((H.lm2_suc).mpr ((H.lm1_suc).mpr (H.lvl_spec hp0))))), hb⟩

theorem t12_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.T12 y c1 c2 k0 v ↔
      (Fm.Ob y (H.lvl v k0) ∧ ¬ (Fm.El y c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ Fm.El y c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)))) := by
  constructor
  · rintro ⟨a, u1, h_a, h_u1, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf h_u1
    exact hb
  · intro hb
    exact ⟨(H.lvl v k0), (H.lvl v (H.suc k0)), (H.lvl_spec hp0), (H.lvl_spec hp1), hb⟩

theorem t13_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) :
    Fm.T13 y c1 c2 k0 v ↔
      (Fm.Ob y (H.lvl v k0) ∧ ∃ r, Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) y r c1) := by
  constructor
  · rintro ⟨a, u1, u2, h_a, h_u1, h_u2, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf h_u1
    obtain rfl := H.lvl_eq hvf h_u2
    exact hb
  · intro hb
    exact ⟨(H.lvl v k0), (H.lvl v (H.suc k0)), (H.lvl v (H.suc (H.suc k0))), (H.lvl_spec hp0), (H.lvl_spec hp1), (H.lvl_spec hp2), hb⟩

theorem t14_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) :
    Fm.T14 y c1 c2 k0 v ↔
      (Fm.Ob y (H.lvl v k0) ∧ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q y c1) := by
  constructor
  · rintro ⟨a, u1, u2, h_a, h_u1, h_u2, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf h_u1
    obtain rfl := H.lvl_eq hvf h_u2
    exact hb
  · intro hb
    exact ⟨(H.lvl v k0), (H.lvl v (H.suc k0)), (H.lvl v (H.suc (H.suc k0))), (H.lvl_spec hp0), (H.lvl_spec hp1), (H.lvl_spec hp2), hb⟩

theorem t15_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.T15 y c1 c2 k0 v ↔
      (Fm.Ob y (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) y c1) := by
  constructor
  · rintro ⟨a, u1, h_a, h_u1, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf h_u1
    exact hb
  · intro hb
    exact ⟨(H.lvl v k0), (H.lvl v (H.suc k0)), (H.lvl_spec hp0), (H.lvl_spec hp1), hb⟩

theorem t16_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.T16 y c1 c2 (H.suc k0) v ↔
      (Fm.Ob y (H.lvl v (H.suc k0)) ∧ ∃ sp P, Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) c1 sp ∧ Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) y sp P ∧ ¬ Fm.El P c2 (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))))) := by
  constructor
  · rintro ⟨a, a1, u1, u2, u3, h_a, h_a1, h_u1, h_u2, h_u3, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf ((H.lm1_suc).mp h_a1)
    obtain rfl := H.lvl_eq hvf h_u1
    obtain rfl := H.lvl_eq hvf h_u2
    obtain rfl := H.lvl_eq hvf h_u3
    exact hb
  · intro hb
    exact ⟨(H.lvl v (H.suc k0)), (H.lvl v k0), (H.lvl v (H.suc (H.suc k0))), (H.lvl v (H.suc (H.suc (H.suc k0)))), (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))), (H.lvl_spec hp1), ((H.lm1_suc).mpr (H.lvl_spec hp0)), (H.lvl_spec hp2), (H.lvl_spec hp3), (H.lvl_spec hp4), hb⟩

theorem t17_iff {v k0 y c1 c2 : H.W} (hvf : H.IsFun v) (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.T17 y c1 c2 k0 v ↔
      (Fm.Ob y (H.lvl v k0) ∧ Fm.El y c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ ¬ Fm.El y c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) := by
  constructor
  · rintro ⟨a, u1, h_a, h_u1, hb⟩
    obtain rfl := H.lvl_eq hvf h_a
    obtain rfl := H.lvl_eq hvf h_u1
    exact hb
  · intro hb
    exact ⟨(H.lvl v k0), (H.lvl v (H.suc k0)), (H.lvl_spec hp0), (H.lvl_spec hp1), hb⟩

theorem val_tm (ar : H.Arith E num) {v : H.W} (i : ℕ) (hi : i < 18) {x y : N}
    {k k1 k2 : H.W} (h1 : H.Sh (off1 i) k k1) (h2 : H.Sh (off2 i) k k2) (hk1 : ∃ b, H.App v k1 b)
    (hk2 : ∃ b, H.App v k2 b) {c : H.W} :
    Fm.Val ar (num (tm i x y)) k v c ↔ ∃ a c1 c2, H.App v k a ∧ Fm.Val ar (num x) k1 v c1 ∧
      Fm.Val ar (num y) k2 v c2 ∧ Fm.Pick num (tg num i) a c (H.op (H.op c1 c2) (H.op k v)) := by
  have hargs : Args ar v (num (tm i x y)) k (tg num i) (num x) (num y) k1 k2 :=
    ⟨ar.dec_tm i x y, (off1_iff num).mpr ⟨i, hi, rfl, h1⟩, (off2_iff num).mpr ⟨i, hi, rfl, h2⟩,
      hk1, hk2⟩
  rw [Fm.val_iff ar]
  constructor
  · rintro ⟨a, ha, h | h⟩
    · obtain ⟨f, n1, n2, j1, j2, c1, c2, h3, h4, h5, h6⟩ := h
      obtain ⟨e1, e2, e3, e4, e5⟩ := args_unique ar h3 hargs
      subst e1 e2 e3 e4 e5
      exact ⟨a, c1, c2, ha, h4, h5, h6⟩
    · exact (h.1 ⟨_, _, _, _, _, hargs⟩).elim
  · rintro ⟨a, c1, c2, ha, h4, h5, h6⟩
    exact ⟨a, ha, Or.inl ⟨_, _, _, _, _, c1, c2, hargs, h4, h5, h6⟩⟩

theorem pick_spec (ar : H.Arith E num) {i : ℕ} (hi : i < 18) {a c c1 c2 k v : H.W}
    (hex : ∃ y, Fm.Tn i y c1 c2 k v)
    (h : Fm.Pick num (tg num i) a c (H.op (H.op c1 c2) (H.op k v))) : Fm.Tn i c c1 c2 k v := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · obtain ⟨j, -, e, hT⟩ := (Fm.th_iff num).mp h1
    rw [tg_inj ar e]
    exact hT
  · obtain ⟨y, hy⟩ := hex
    exact (h1 ⟨y, (Fm.th_iff num).mpr ⟨i, hi, rfl, hy⟩⟩).elim

/-- The value of a term at a position is an object of the level at that position. -/
theorem val_ob (ar : H.Arith E num) {v n k c : H.W} (hv : Fm.Plc v) (h : Fm.Val ar n k v c) :
    Fm.Ob c (H.lvl v k) := by
  obtain ⟨a, ha, h⟩ := (Fm.val_iff ar).mp h
  have ea := H.lvl_eq hv.fn ha
  subst ea
  rcases h with ⟨f, n1, n2, k1, k2, c1, c2, -, -, -, hp⟩ | ⟨-, h⟩
  · rcases hp with ⟨h1, -⟩ | ⟨-, h1⟩
    · obtain ⟨j, -, -, hT⟩ := (Fm.th_iff num).mp h1
      obtain ⟨a', ha', hob⟩ := tn_ob j hT
      rw [← H.lvl_eq hv.fn ha']
      exact hob
    · exact h1.1
  · exact h.1

theorem val0_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hx : Fm.Val ar (num x) k0 v c1) (hy : Fm.Val ar (num y) (H.suc k0) v c2)
    (hex : ∃ y', Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) c1 y')
    (hval : Fm.Val ar (num (tm 0 x y)) (H.suc k0) v c) :
    Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) c1 c := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 0 (by decide) rfl rfl hp0 hp1).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T0 c d1 d2 (H.suc k0) v := pick_spec ar (by decide : 0 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T0 y' d1 d2 (H.suc k0) v from (t0_iff hv.fn hp0 hp1).mpr hy'⟩) hpick
  exact (t0_iff hv.fn hp0 hp1).mp hT

theorem val1_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hx : Fm.Val ar (num x) k0 v c1) (hy : Fm.Val ar (num y) k0 v c2)
    (hex : ∃ y', Fm.IsUp (H.lvl v (H.suc k0)) (H.lvl v k0) c1 c2 y')
    (hval : Fm.Val ar (num (tm 1 x y)) (H.suc k0) v c) :
    Fm.IsUp (H.lvl v (H.suc k0)) (H.lvl v k0) c1 c2 c := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 1 (by decide) rfl rfl hp0 hp0).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T1 c d1 d2 (H.suc k0) v := pick_spec ar (by decide : 1 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T1 y' d1 d2 (H.suc k0) v from (t1_iff hv.fn hp0 hp1).mpr hy'⟩) hpick
  exact (t1_iff hv.fn hp0 hp1).mp hT

theorem val2_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hx : Fm.Val ar (num x) (H.suc k0) v c1) (hy : Fm.Val ar (num y) (H.suc k0) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z y' (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      Fm.El z c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ Fm.El z c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))))
    (hval : Fm.Val ar (num (tm 2 x y)) (H.suc k0) v c) :
    Fm.Ob c (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z c (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      Fm.El z c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ Fm.El z c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 2 (by decide) rfl rfl hp1 hp1).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T2 c d1 d2 (H.suc k0) v := pick_spec ar (by decide : 2 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T2 y' d1 d2 (H.suc k0) v from (t2_iff hv.fn hp0 hp1).mpr hy'⟩) hpick
  exact (t2_iff hv.fn hp0 hp1).mp hT

theorem val3_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hx : Fm.Val ar (num x) (H.suc k0) v c1) (hy : Fm.Val ar (num y) (H.suc k0) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z y' (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ ¬ Fm.El z c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))))
    (hval : Fm.Val ar (num (tm 3 x y)) (H.suc k0) v c) :
    Fm.Ob c (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z c (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ ¬ Fm.El z c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 3 (by decide) rfl rfl hp1 hp1).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T3 c d1 d2 (H.suc k0) v := pick_spec ar (by decide : 3 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T3 y' d1 d2 (H.suc k0) v from (t3_iff hv.fn hp0 hp1).mpr hy'⟩) hpick
  exact (t3_iff hv.fn hp0 hp1).mp hT

theorem val4_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc (H.suc k0))) v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc (H.suc (H.suc k0)))) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ z w sz sw P Q, Fm.Ob z (H.lvl v k0) → Fm.Ob w (H.lvl v k0) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) z sz →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) w sw → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sz sw P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) z w Q →
      (Fm.El P y' (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ Fm.El Q c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))))
    (hval : Fm.Val ar (num (tm 4 x y)) (H.suc (H.suc (H.suc (H.suc k0)))) v c) :
    Fm.Ob c (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ z w sz sw P Q, Fm.Ob z (H.lvl v k0) → Fm.Ob w (H.lvl v k0) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) z sz →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) w sw → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sz sw P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) z w Q →
      (Fm.El P c (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ Fm.El Q c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 4 (by decide) rfl rfl hp3 hp4).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T4 c d1 d2 (H.suc (H.suc (H.suc (H.suc k0)))) v := pick_spec ar (by decide : 4 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T4 y' d1 d2 (H.suc (H.suc (H.suc (H.suc k0)))) v from (t4_iff hv.fn hp0 hp1 hp2 hp3 hp4).mpr hy'⟩) hpick
  exact (t4_iff hv.fn hp0 hp1 hp2 hp3 hp4).mp hT

theorem val5_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc (H.suc k0))) v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opr, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p r opr →
      (Fm.El P y' (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opr c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))))
    (hval : Fm.Val ar (num (tm 5 x y)) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v c) :
    Fm.Ob c (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opr, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p r opr →
      (Fm.El P c (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opr c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 5 (by decide) rfl rfl hp3 hp5).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T5 c d1 d2 (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v := pick_spec ar (by decide : 5 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T5 y' d1 d2 (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v from (t5_iff hv.fn hp0 hp1 hp2 hp3 hp4 hp5).mpr hy'⟩) hpick
  exact (t5_iff hv.fn hp0 hp1 hp2 hp3 hp4 hp5).mp hT

theorem val6_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc (H.suc k0))) v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opq, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q opq →
      (Fm.El P y' (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opq c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))))
    (hval : Fm.Val ar (num (tm 6 x y)) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v c) :
    Fm.Ob c (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opq, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q opq →
      (Fm.El P c (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opq c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 6 (by decide) rfl rfl hp3 hp5).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T6 c d1 d2 (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v := pick_spec ar (by decide : 6 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T6 y' d1 d2 (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v from (t6_iff hv.fn hp0 hp1 hp2 hp3 hp4 hp5).mpr hy'⟩) hpick
  exact (t6_iff hv.fn hp0 hp1 hp2 hp3 hp4 hp5).mp hT

theorem val7_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b)
    (hx : Fm.Val ar (num x) (H.suc k0) v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc (H.suc k0))) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc (H.suc k0))) → (Fm.El p y' (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔
      ∃ q r, Fm.Ob q (H.lvl v k0) ∧ Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r p ∧ Fm.El r c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))))
    (hval : Fm.Val ar (num (tm 7 x y)) (H.suc (H.suc (H.suc k0))) v c) :
    Fm.Ob c (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc (H.suc k0))) → (Fm.El p c (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔
      ∃ q r, Fm.Ob q (H.lvl v k0) ∧ Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r p ∧ Fm.El r c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 7 (by decide) rfl rfl hp1 hp3).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T7 c d1 d2 (H.suc (H.suc (H.suc k0))) v := pick_spec ar (by decide : 7 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T7 y' d1 d2 (H.suc (H.suc (H.suc k0))) v from (t7_iff hv.fn hp0 hp1 hp2 hp3).mpr hy'⟩) hpick
  exact (t7_iff hv.fn hp0 hp1 hp2 hp3).mp hT

theorem val8_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc (H.suc (H.suc k0)))) v c1) (hy : Fm.Val ar (num y) (H.suc k0) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc k0)) ∧ ∀ p, Fm.Ob p (H.lvl v k0) → (Fm.El p y' (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      ∀ q sp P, Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) q sp P → Fm.El P c1 (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))))))
    (hval : Fm.Val ar (num (tm 8 x y)) (H.suc k0) v c) :
    Fm.Ob c (H.lvl v (H.suc k0)) ∧ ∀ p, Fm.Ob p (H.lvl v k0) → (Fm.El p c (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      ∀ q sp P, Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) q sp P → Fm.El P c1 (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 8 (by decide) rfl rfl hp4 hp1).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T8 c d1 d2 (H.suc k0) v := pick_spec ar (by decide : 8 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T8 y' d1 d2 (H.suc k0) v from (t8_iff hv.fn hp0 hp1 hp2 hp3 hp4).mpr hy'⟩) hpick
  exact (t8_iff hv.fn hp0 hp1 hp2 hp3 hp4).mp hT

theorem val9_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc (H.suc k0))) v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc (H.suc k0))) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p q r r', Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q r →
      Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q p r' → (Fm.El r y' (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔ Fm.El r' c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))))
    (hval : Fm.Val ar (num (tm 9 x y)) (H.suc (H.suc (H.suc k0))) v c) :
    Fm.Ob c (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p q r r', Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q r →
      Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q p r' → (Fm.El r c (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔ Fm.El r' c1 (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 9 (by decide) rfl rfl hp3 hp3).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T9 c d1 d2 (H.suc (H.suc (H.suc k0))) v := pick_spec ar (by decide : 9 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T9 y' d1 d2 (H.suc (H.suc (H.suc k0))) v from (t9_iff hv.fn hp0 hp1 hp2 hp3).mpr hy'⟩) hpick
  exact (t9_iff hv.fn hp0 hp1 hp2 hp3).mp hT

theorem val10_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc k0)) v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc k0)) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc (H.suc k0))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc k0)) → (Fm.El p y' (H.op (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0))) ↔ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) q p))
    (hval : Fm.Val ar (num (tm 10 x y)) (H.suc (H.suc k0)) v c) :
    Fm.Ob c (H.lvl v (H.suc (H.suc k0))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc k0)) → (Fm.El p c (H.op (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0))) ↔ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) q p) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 10 (by decide) rfl rfl hp2 hp2).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T10 c d1 d2 (H.suc (H.suc k0)) v := pick_spec ar (by decide : 10 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T10 y' d1 d2 (H.suc (H.suc k0)) v from (t10_iff hv.fn hp0 hp1 hp2).mpr hy'⟩) hpick
  exact (t10_iff hv.fn hp0 hp1 hp2).mp hT

theorem val11_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc (H.suc (H.suc k0)))) v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc (H.suc (H.suc k0)))) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ p q o, Fm.Ob p (H.lvl v (H.suc k0)) → Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) p q o →
      (Fm.El o y' (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ ∀ r, Fm.Ob r (H.lvl v k0) → Fm.El r p (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) → Fm.El r q (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))))
    (hval : Fm.Val ar (num (tm 11 x y)) (H.suc (H.suc (H.suc (H.suc k0)))) v c) :
    Fm.Ob c (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ p q o, Fm.Ob p (H.lvl v (H.suc k0)) → Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) p q o →
      (Fm.El o c (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ ∀ r, Fm.Ob r (H.lvl v k0) → Fm.El r p (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) → Fm.El r q (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 11 (by decide) rfl rfl hp4 hp4).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T11 c d1 d2 (H.suc (H.suc (H.suc (H.suc k0)))) v := pick_spec ar (by decide : 11 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T11 y' d1 d2 (H.suc (H.suc (H.suc (H.suc k0)))) v from (t11_iff hv.fn hp0 hp1 hp2 hp3 hp4).mpr hy'⟩) hpick
  exact (t11_iff hv.fn hp0 hp1 hp2 hp3 hp4).mp hT

theorem val12_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hx : Fm.Val ar (num x) (H.suc k0) v c1) (hy : Fm.Val ar (num y) (H.suc k0) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ ¬ (Fm.El y' c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ Fm.El y' c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))))
    (hval : Fm.Val ar (num (tm 12 x y)) k0 v c) :
    Fm.Ob c (H.lvl v k0) ∧ ¬ (Fm.El c c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ Fm.El c c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 12 (by decide) rfl rfl hp1 hp1).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T12 c d1 d2 k0 v := pick_spec ar (by decide : 12 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T12 y' d1 d2 k0 v from (t12_iff hv.fn hp0 hp1).mpr hy'⟩) hpick
  exact (t12_iff hv.fn hp0 hp1).mp hT

theorem val13_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc k0)) v c1) (hy : Fm.Val ar (num y) k0 v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ ∃ r, Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) y' r c1)
    (hval : Fm.Val ar (num (tm 13 x y)) k0 v c) :
    Fm.Ob c (H.lvl v k0) ∧ ∃ r, Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) c r c1 := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 13 (by decide) rfl rfl hp2 hp0).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T13 c d1 d2 k0 v := pick_spec ar (by decide : 13 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T13 y' d1 d2 k0 v from (t13_iff hv.fn hp0 hp1 hp2).mpr hy'⟩) hpick
  exact (t13_iff hv.fn hp0 hp1 hp2).mp hT

theorem val14_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b)
    (hx : Fm.Val ar (num x) (H.suc (H.suc k0)) v c1) (hy : Fm.Val ar (num y) k0 v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q y' c1)
    (hval : Fm.Val ar (num (tm 14 x y)) k0 v c) :
    Fm.Ob c (H.lvl v k0) ∧ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q c c1 := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 14 (by decide) rfl rfl hp2 hp0).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T14 c d1 d2 k0 v := pick_spec ar (by decide : 14 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T14 y' d1 d2 k0 v from (t14_iff hv.fn hp0 hp1 hp2).mpr hy'⟩) hpick
  exact (t14_iff hv.fn hp0 hp1 hp2).mp hT

theorem val15_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hx : Fm.Val ar (num x) (H.suc k0) v c1) (hy : Fm.Val ar (num y) k0 v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) y' c1)
    (hval : Fm.Val ar (num (tm 15 x y)) k0 v c) :
    Fm.Ob c (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) c c1 := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 15 (by decide) rfl rfl hp1 hp0).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T15 c d1 d2 k0 v := pick_spec ar (by decide : 15 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T15 y' d1 d2 k0 v from (t15_iff hv.fn hp0 hp1).mpr hy'⟩) hpick
  exact (t15_iff hv.fn hp0 hp1).mp hT

theorem val16_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (hx : Fm.Val ar (num x) k0 v c1) (hy : Fm.Val ar (num y) (H.suc (H.suc (H.suc (H.suc k0)))) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc k0)) ∧ ∃ sp P, Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) c1 sp ∧ Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) y' sp P ∧ ¬ Fm.El P c2 (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))))
    (hval : Fm.Val ar (num (tm 16 x y)) (H.suc k0) v c) :
    Fm.Ob c (H.lvl v (H.suc k0)) ∧ ∃ sp P, Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) c1 sp ∧ Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) c sp P ∧ ¬ Fm.El P c2 (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 16 (by decide) rfl rfl hp0 hp4).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T16 c d1 d2 (H.suc k0) v := pick_spec ar (by decide : 16 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T16 y' d1 d2 (H.suc k0) v from (t16_iff hv.fn hp0 hp1 hp2 hp3 hp4).mpr hy'⟩) hpick
  exact (t16_iff hv.fn hp0 hp1 hp2 hp3 hp4).mp hT

theorem val17_spec (ar : H.Arith E num) {v k0 c c1 c2 : H.W} {x y : N} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hx : Fm.Val ar (num x) (H.suc k0) v c1) (hy : Fm.Val ar (num y) (H.suc k0) v c2)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ Fm.El y' c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ ¬ Fm.El y' c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)))
    (hval : Fm.Val ar (num (tm 17 x y)) k0 v c) :
    Fm.Ob c (H.lvl v k0) ∧ Fm.El c c1 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ ¬ Fm.El c c2 (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) := by
  obtain ⟨a, d1, d2, ha, hd1, hd2, hpick⟩ := (val_tm ar 17 (by decide) rfl rfl hp1 hp1).mp hval
  have e1 := Fm.val_fun ar hv.fn _ _ _ _ hd1 hx
  have e2 := Fm.val_fun ar hv.fn _ _ _ _ hd2 hy
  subst e1 e2
  have hT : Fm.T17 c d1 d2 k0 v := pick_spec ar (by decide : 17 < 18)
    (by obtain ⟨y', hy'⟩ := hex; exact ⟨y', show Fm.T17 y' d1 d2 k0 v from (t17_iff hv.fn hp0 hp1).mpr hy'⟩) hpick
  exact (t17_iff hv.fn hp0 hp1).mp hT

end FlatM

/-! ## Phase 2 (A5, generated): the value of a term as a function, and what the value of each
symbol satisfies

Generated by `gen/gen47.py`. -/

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- A position below a position of a placement is a position. -/
theorem Plc.down {v k : H.W} (hv : Fm.Plc v) (h : ∃ b, H.App v (H.suc k) b) : ∃ b, H.App v k b := by
  obtain ⟨L, hL⟩ := hv.seq
  obtain ⟨b, hb⟩ := h
  exact hL.tot (H.om_mem_trans hL.2.1 (hL.dom hb) (H.mem_suc.mpr (Or.inr rfl)))

/-- The value of the term `n` at the position `k` of the placement `v`. -/
noncomputable def vl (Fm : FlatM H) (ar : H.Arith E num) (n k v : H.W) : H.W :=
  open Classical in if h : ∃ c, Fm.Val ar n k v c then Classical.choose h else k

theorem vl_spec (ar : H.Arith E num) (ax : Fm.Ax) {v k : H.W} {n : H.W} (hv : Fm.Plc v)
    (hk : ∃ b, H.App v k b) : Fm.Val ar n k v (Fm.vl ar n k v) := by
  obtain ⟨b, hb⟩ := hk
  have h := FlatM.val_tot ax ar hv.lv n k b hb
  unfold vl
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem val_eq (ar : H.Arith E num) (ax : Fm.Ax) {v k n c : H.W} (hv : Fm.Plc v)
    (h : Fm.Val ar n k v c) : c = Fm.vl ar n k v := by
  obtain ⟨a, ha, -⟩ := (Fm.val_iff ar).mp h
  exact FlatM.val_fun ar hv.fn _ _ _ _ h (vl_spec ar ax hv ⟨a, ha⟩)

theorem vl_ob (ar : H.Arith E num) (ax : Fm.Ax) {v k : H.W} {n : H.W} (hv : Fm.Plc v)
    (hk : ∃ b, H.App v k b) : Fm.Ob (Fm.vl ar n k v) (H.lvl v k) :=
  val_ob ar hv (vl_spec ar ax hv hk)

theorem vs0 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num x) k0 v) (Fm.vl ar (num (tm 0 x y)) (H.suc k0) v) :=
  val0_spec ar hv hp0 hp1 (vl_spec ar ax hv hp0) (vl_spec ar ax hv hp1)
    (ax.sing _ _ _ (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp0)) (vl_spec ar ax hv hp1)

theorem vs1 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.IsUp (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num x) k0 v) (Fm.vl ar (num y) k0 v) (Fm.vl ar (num (tm 1 x y)) (H.suc k0) v) :=
  val1_spec ar hv hp0 hp1 (vl_spec ar ax hv hp0) (vl_spec ar ax hv hp0)
    (ax.up _ _ _ _ (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp0) (vl_ob ar ax hv hp0)) (vl_spec ar ax hv hp1)

theorem vs2 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.Ob (Fm.vl ar (num (tm 2 x y)) (H.suc k0) v) (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z (Fm.vl ar (num (tm 2 x y)) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      Fm.El z (Fm.vl ar (num x) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ Fm.El z (Fm.vl ar (num y) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) :=
  val2_spec ar hv hp0 hp1 (vl_spec ar ax hv hp1) (vl_spec ar ax hv hp1)
    (ax.inter _ _ _ _ (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp1) (vl_ob ar ax hv hp1)) (vl_spec ar ax hv hp1)

theorem vs3 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.Ob (Fm.vl ar (num (tm 3 x y)) (H.suc k0) v) (H.lvl v (H.suc k0)) ∧ ∀ z, Fm.Ob z (H.lvl v k0) → (Fm.El z (Fm.vl ar (num (tm 3 x y)) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ ¬ Fm.El z (Fm.vl ar (num x) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) :=
  val3_spec ar hv hp0 hp1 (vl_spec ar ax hv hp1) (vl_spec ar ax hv hp1)
    (ax.compl _ _ _ (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp1)) (vl_spec ar ax hv hp1)

theorem vs4 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.Ob (Fm.vl ar (num (tm 4 x y)) (H.suc (H.suc (H.suc (H.suc k0)))) v) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ z w sz sw P Q, Fm.Ob z (H.lvl v k0) → Fm.Ob w (H.lvl v k0) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) z sz →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) w sw → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sz sw P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) z w Q →
      (Fm.El P (Fm.vl ar (num (tm 4 x y)) (H.suc (H.suc (H.suc (H.suc k0)))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ Fm.El Q (Fm.vl ar (num x) (H.suc (H.suc (H.suc k0))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) :=
  val4_spec ar hv hp0 hp1 hp2 hp3 hp4 (vl_spec ar ax hv hp3) (vl_spec ar ax hv hp4)
    (ax.singletonImage _ _ _ _ _ _ (plc_lt hv hp3 hp4) (plc_lt hv hp2 hp3) (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp3)) (vl_spec ar ax hv hp4)

theorem vs5 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b) :
    Fm.Ob (Fm.vl ar (num (tm 5 x y)) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v) (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opr, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p r opr →
      (Fm.El P (Fm.vl ar (num (tm 5 x y)) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opr (Fm.vl ar (num x) (H.suc (H.suc (H.suc k0))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) :=
  val5_spec ar hv hp0 hp1 hp2 hp3 hp4 hp5 (vl_spec ar ax hv hp3) (vl_spec ar ax hv hp5)
    (ax.insertion2 _ _ _ _ _ _ _ (plc_lt hv hp4 hp5) (plc_lt hv hp3 hp4) (plc_lt hv hp2 hp3) (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp3)) (vl_spec ar ax hv hp5)

theorem vs6 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b) :
    Fm.Ob (Fm.vl ar (num (tm 6 x y)) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v) (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) ∧ ∀ p q r sp ssp oqr P opq, Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.Ob r (H.lvl v k0) →
      Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsSg (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) sp ssp → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r oqr →
      Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) ssp oqr P → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q opq →
      (Fm.El P (Fm.vl ar (num (tm 6 x y)) (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc (H.suc k0)))))) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0)))))) ↔ Fm.El opq (Fm.vl ar (num x) (H.suc (H.suc (H.suc k0))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) :=
  val6_spec ar hv hp0 hp1 hp2 hp3 hp4 hp5 (vl_spec ar ax hv hp3) (vl_spec ar ax hv hp5)
    (ax.insertion3 _ _ _ _ _ _ _ (plc_lt hv hp4 hp5) (plc_lt hv hp3 hp4) (plc_lt hv hp2 hp3) (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp3)) (vl_spec ar ax hv hp5)

theorem vs7 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) :
    Fm.Ob (Fm.vl ar (num (tm 7 x y)) (H.suc (H.suc (H.suc k0))) v) (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc (H.suc k0))) → (Fm.El p (Fm.vl ar (num (tm 7 x y)) (H.suc (H.suc (H.suc k0))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔
      ∃ q r, Fm.Ob q (H.lvl v k0) ∧ Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q r p ∧ Fm.El r (Fm.vl ar (num x) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) :=
  val7_spec ar hv hp0 hp1 hp2 hp3 (vl_spec ar ax hv hp1) (vl_spec ar ax hv hp3)
    (ax.vCross _ _ _ _ _ (plc_lt hv hp2 hp3) (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp1)) (vl_spec ar ax hv hp3)

theorem vs8 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.Ob (Fm.vl ar (num (tm 8 x y)) (H.suc k0) v) (H.lvl v (H.suc k0)) ∧ ∀ p, Fm.Ob p (H.lvl v k0) → (Fm.El p (Fm.vl ar (num (tm 8 x y)) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      ∀ q sp P, Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) p sp → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) q sp P → Fm.El P (Fm.vl ar (num x) (H.suc (H.suc (H.suc (H.suc k0)))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))))) :=
  val8_spec ar hv hp0 hp1 hp2 hp3 hp4 (vl_spec ar ax hv hp4) (vl_spec ar ax hv hp1)
    (ax.typeLower _ _ _ _ _ _ (plc_lt hv hp3 hp4) (plc_lt hv hp2 hp3) (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp4)) (vl_spec ar ax hv hp1)

theorem vs9 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) :
    Fm.Ob (Fm.vl ar (num (tm 9 x y)) (H.suc (H.suc (H.suc k0))) v) (H.lvl v (H.suc (H.suc (H.suc k0)))) ∧ ∀ p q r r', Fm.Ob p (H.lvl v k0) → Fm.Ob q (H.lvl v k0) → Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) p q r →
      Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q p r' → (Fm.El r (Fm.vl ar (num (tm 9 x y)) (H.suc (H.suc (H.suc k0))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0)))) ↔ Fm.El r' (Fm.vl ar (num x) (H.suc (H.suc (H.suc k0))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))))) :=
  val9_spec ar hv hp0 hp1 hp2 hp3 (vl_spec ar ax hv hp3) (vl_spec ar ax hv hp3)
    (ax.converse _ _ _ _ _ (plc_lt hv hp2 hp3) (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp3)) (vl_spec ar ax hv hp3)

theorem vs10 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) :
    Fm.Ob (Fm.vl ar (num (tm 10 x y)) (H.suc (H.suc k0)) v) (H.lvl v (H.suc (H.suc k0))) ∧ ∀ p, Fm.Ob p (H.lvl v (H.suc k0)) → (Fm.El p (Fm.vl ar (num (tm 10 x y)) (H.suc (H.suc k0)) v) (H.op (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0))) ↔ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) q p) :=
  val10_spec ar hv hp0 hp1 hp2 (vl_spec ar ax hv hp2) (vl_spec ar ax hv hp2)
    (ax.cardinalOne _ _ _ (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1)) (vl_spec ar ax hv hp2)

theorem vs11 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.Ob (Fm.vl ar (num (tm 11 x y)) (H.suc (H.suc (H.suc (H.suc k0)))) v) (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) ∧ ∀ p q o, Fm.Ob p (H.lvl v (H.suc k0)) → Fm.Ob q (H.lvl v (H.suc k0)) → Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) p q o →
      (Fm.El o (Fm.vl ar (num (tm 11 x y)) (H.suc (H.suc (H.suc (H.suc k0)))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) ↔ ∀ r, Fm.Ob r (H.lvl v k0) → Fm.El r p (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) → Fm.El r q (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) :=
  val11_spec ar hv hp0 hp1 hp2 hp3 hp4 (vl_spec ar ax hv hp4) (vl_spec ar ax hv hp4)
    (ax.subset _ _ _ _ _ (plc_lt hv hp3 hp4) (plc_lt hv hp2 hp3) (plc_lt hv hp1 hp2) (plc_lt hv hp0 hp1)) (vl_spec ar ax hv hp4)

theorem vs12 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ ¬ (Fm.El y' (Fm.vl ar (num x) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ Fm.El y' (Fm.vl ar (num y) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)))) :
    Fm.Ob (Fm.vl ar (num (tm 12 x y)) k0 v) (H.lvl v k0) ∧ ¬ (Fm.El (Fm.vl ar (num (tm 12 x y)) k0 v) (Fm.vl ar (num x) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔ Fm.El (Fm.vl ar (num (tm 12 x y)) k0 v) (Fm.vl ar (num y) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) :=
  val12_spec ar hv hp0 hp1 (vl_spec ar ax hv hp1) (vl_spec ar ax hv hp1)
    hex (vl_spec ar ax hv hp0)

theorem vs13 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ ∃ r, Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) y' r (Fm.vl ar (num x) (H.suc (H.suc k0)) v)) :
    Fm.Ob (Fm.vl ar (num (tm 13 x y)) k0 v) (H.lvl v k0) ∧ ∃ r, Fm.Ob r (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num (tm 13 x y)) k0 v) r (Fm.vl ar (num x) (H.suc (H.suc k0)) v) :=
  val13_spec ar hv hp0 hp1 hp2 (vl_spec ar ax hv hp2) (vl_spec ar ax hv hp0)
    hex (vl_spec ar ax hv hp0)

theorem vs14 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q y' (Fm.vl ar (num x) (H.suc (H.suc k0)) v)) :
    Fm.Ob (Fm.vl ar (num (tm 14 x y)) k0 v) (H.lvl v k0) ∧ ∃ q, Fm.Ob q (H.lvl v k0) ∧ Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) q (Fm.vl ar (num (tm 14 x y)) k0 v) (Fm.vl ar (num x) (H.suc (H.suc k0)) v) :=
  val14_spec ar hv hp0 hp1 hp2 (vl_spec ar ax hv hp2) (vl_spec ar ax hv hp0)
    hex (vl_spec ar ax hv hp0)

theorem vs15 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) y' (Fm.vl ar (num x) (H.suc k0) v)) :
    Fm.Ob (Fm.vl ar (num (tm 15 x y)) k0 v) (H.lvl v k0) ∧ Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num (tm 15 x y)) k0 v) (Fm.vl ar (num x) (H.suc k0) v) :=
  val15_spec ar hv hp0 hp1 (vl_spec ar ax hv hp1) (vl_spec ar ax hv hp0)
    hex (vl_spec ar ax hv hp0)

theorem vs16 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b) (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (hex : ∃ y', Fm.Ob y' (H.lvl v (H.suc k0)) ∧ ∃ sp P, Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num x) k0 v) sp ∧ Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) y' sp P ∧ ¬ Fm.El P (Fm.vl ar (num y) (H.suc (H.suc (H.suc (H.suc k0)))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0)))))) :
    Fm.Ob (Fm.vl ar (num (tm 16 x y)) (H.suc k0) v) (H.lvl v (H.suc k0)) ∧ ∃ sp P, Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num x) k0 v) sp ∧ Fm.IsOp (H.lvl v (H.suc (H.suc (H.suc k0)))) (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (Fm.vl ar (num (tm 16 x y)) (H.suc k0) v) sp P ∧ ¬ Fm.El P (Fm.vl ar (num y) (H.suc (H.suc (H.suc (H.suc k0)))) v) (H.op (H.lvl v (H.suc (H.suc (H.suc (H.suc k0))))) (H.lvl v (H.suc (H.suc (H.suc k0))))) :=
  val16_spec ar hv hp0 hp1 hp2 hp3 hp4 (vl_spec ar ax hv hp0) (vl_spec ar ax hv hp4)
    hex (vl_spec ar ax hv hp1)

theorem vs17 (ar : H.Arith E num) (ax : Fm.Ax) {v k0 : H.W} (x y : N) (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k0 b) (hp1 : ∃ b, H.App v (H.suc k0) b)
    (hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ Fm.El y' (Fm.vl ar (num x) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ ¬ Fm.El y' (Fm.vl ar (num y) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) :
    Fm.Ob (Fm.vl ar (num (tm 17 x y)) k0 v) (H.lvl v k0) ∧ Fm.El (Fm.vl ar (num (tm 17 x y)) k0 v) (Fm.vl ar (num x) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ∧ ¬ Fm.El (Fm.vl ar (num (tm 17 x y)) k0 v) (Fm.vl ar (num y) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) :=
  val17_spec ar hv hp0 hp1 (vl_spec ar ax hv hp1) (vl_spec ar ax hv hp1)
    hex (vl_spec ar ax hv hp0)

end FlatM

/-! ## Phase 2 (A5): the axioms N at shifted positions

Written through `gen/gen48.py`, which only expands the abbreviations for positions, levels
and values. -/

section terms

variable {N : Type} [CommSemiring N]

/-- The terms. -/
def sgT (x : N) : N := tm 0 x 0
def upT (x y : N) : N := tm 1 x y
def opT (x y : N) : N := upT (sgT x) (upT x y)
def inT (x y : N) : N := tm 2 x y
def coT (x : N) : N := tm 3 x 0
def siT (x : N) : N := tm 4 x 0
def i2T (x : N) : N := tm 5 x 0
def i3T (x : N) : N := tm 6 x 0
def vcT (x : N) : N := tm 7 x 0
def tlT (x : N) : N := tm 8 x 0
def cvT (x : N) : N := tm 9 x 0
def c1T : N := tm 10 0 0
def sbT : N := tm 11 0 0
def dT (x y : N) : N := tm 12 x y
def p1T (p : N) : N := tm 13 p 0
def p2T (p : N) : N := tm 14 p 0
def elT (p : N) : N := tm 15 p 0
def wtT (p x : N) : N := tm 16 p x
def wsT (p q : N) : N := tm 17 p q

end terms

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- The atom `t ∈ t'` at the position `k`: the value of `t` at `k` is a member of the value of
`t'` at the next position. -/
def Tin (Fm : FlatM H) (ar : H.Arith E num) (t t' : N) (k v : H.W) : Prop :=
  Fm.El (Fm.vl ar (num t) k v) (Fm.vl ar (num t') (H.suc k) v) (H.op (H.lvl v (H.suc k)) (H.lvl v k))

/-- The atom `t = t'` at the position `k`. -/
def Teq (Fm : FlatM H) (ar : H.Arith E num) (t t' : N) (k v : H.W) : Prop :=
  Fm.vl ar (num t) k v = Fm.vl ar (num t') k v

variable (ar : H.Arith E num) (ax : Fm.Ax) {v : H.W} (hv : Fm.Plc v)
include ax hv

theorem vl_sg (x : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.IsSg (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num (x)) k0 v) (Fm.vl ar (num (sgT x)) (H.suc k0) v) :=
  vs0 ar ax x 0 hv (hv.down hp1) hp1

theorem vl_up (x y : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.IsUp (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num (x)) k0 v) (Fm.vl ar (num (y)) k0 v) (Fm.vl ar (num (upT x y)) (H.suc k0) v) :=
  vs1 ar ax x y hv (hv.down hp1) hp1

theorem vl_op (x y : N) {k0 : H.W} (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b) :
    Fm.IsOp (H.lvl v (H.suc (H.suc k0))) (H.lvl v (H.suc k0)) (H.lvl v k0) (Fm.vl ar (num (x)) k0 v) (Fm.vl ar (num (y)) k0 v) (Fm.vl ar (num (opT x y)) (H.suc (H.suc k0)) v) :=
  ⟨_, _, vl_sg ar ax hv x (hv.down hp2), vl_up ar ax hv x y (hv.down hp2),
    vl_up ar ax hv (sgT x) (upT x y) hp2⟩

omit ax hv in
theorem n_e1 (x : N) (k v : H.W) : Fm.Teq ar x x k v := rfl

omit ax hv in
theorem n_e2 {x y z : N} {k v : H.W} (h1 : Fm.Teq ar x y k v) (h2 : Fm.Teq ar x z k v) :
    Fm.Teq ar y z k v := h1.symm.trans h2

omit ax hv in
theorem n_e3 {x x' y y' : N} {k v : H.W} (h1 : Fm.Teq ar x x' k v)
    (h2 : Fm.Teq ar y y' (H.suc k) v) (h : Fm.Tin ar x y k v) : Fm.Tin ar x' y' k v := by
  unfold Teq at h1 h2
  unfold Tin at h ⊢
  rw [← h1, ← h2]
  exact h

theorem n_e4a (x x' : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) (h : Fm.Teq ar x x' k0 v) :
    Fm.Teq ar (sgT x) (sgT x') (H.suc k0) v := by
  have h1 := vl_sg ar ax hv x hp1
  have h2 := vl_sg ar ax hv x' hp1
  unfold Teq at h ⊢
  rw [← h] at h2
  exact sg_unique ax (plc_lt hv (hv.down hp1) hp1) h1 h2

theorem n_e4b (x x' y y' : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) (h : Fm.Teq ar x x' k0 v)
    (h' : Fm.Teq ar y y' k0 v) : Fm.Teq ar (upT x y) (upT x' y') (H.suc k0) v := by
  have h1 := vl_up ar ax hv x y hp1
  have h2 := vl_up ar ax hv x' y' hp1
  unfold Teq at h h' ⊢
  rw [← h, ← h'] at h2
  exact up_unique ax (plc_lt hv (hv.down hp1) hp1) h1 h2

theorem n_m1 (x y : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b)
    (h : Fm.Tin ar (dT x y) x k0 v ↔ Fm.Tin ar (dT x y) y k0 v) : Fm.Teq ar x y (H.suc k0) v := by
  unfold Teq
  by_contra hne
  have hp0 := hv.down hp1
  have hex : ∃ y', Fm.Ob y' (H.lvl v k0) ∧ ¬ (Fm.El y' (Fm.vl ar (num (x)) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0)) ↔
      Fm.El y' (Fm.vl ar (num (y)) (H.suc k0) v) (H.op (H.lvl v (H.suc k0)) (H.lvl v k0))) := by
    by_contra hno
    refine hne (ax.ext _ _ _ _ (plc_lt hv hp0 hp1) (vl_ob ar ax hv hp1) (vl_ob ar ax hv hp1)
      fun z hz => ?_)
    by_contra hz'
    exact hno ⟨z, hz, hz'⟩
  exact (vs12 ar ax x y hv hp0 hp1 hex).2 h

theorem n_m2 (x y : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.Tin ar y (sgT x) k0 v ↔ Fm.Teq ar y x k0 v :=
  (vl_sg ar ax hv x hp1).2 _ (vl_ob ar ax hv (hv.down hp1))

theorem n_m3 (x y z : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.Tin ar z (upT x y) k0 v ↔ Fm.Teq ar z x k0 v ∨ Fm.Teq ar z y k0 v :=
  (vl_up ar ax hv x y hp1).2 _ (vl_ob ar ax hv (hv.down hp1))

theorem n_m4 (x y z : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.Tin ar z (inT x y) k0 v ↔ Fm.Tin ar z x k0 v ∧ Fm.Tin ar z y k0 v :=
  (vs2 ar ax x y hv (hv.down hp1) hp1).2 _ (vl_ob ar ax hv (hv.down hp1))

theorem n_m5 (x z : N) {k0 : H.W} (hp1 : ∃ b, H.App v (H.suc k0) b) :
    Fm.Tin ar z (coT x) k0 v ↔ ¬ Fm.Tin ar z x k0 v :=
  (vs3 ar ax x 0 hv (hv.down hp1) hp1).2 _ (vl_ob ar ax hv (hv.down hp1))

theorem n_m6 (x z w : N) {k0 : H.W} (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b) :
    Fm.Tin ar (opT (sgT z) (sgT w)) (siT x) (H.suc (H.suc (H.suc k0))) v ↔ Fm.Tin ar (opT z w) x (H.suc (H.suc k0)) v := by
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  exact (vs4 ar ax x 0 hv hp0 hp1 hp2 hp3 hp4).2 (Fm.vl ar (num (z)) k0 v) (Fm.vl ar (num (w)) k0 v) (Fm.vl ar (num (sgT z)) (H.suc k0) v) (Fm.vl ar (num (sgT w)) (H.suc k0) v) _ _
    (vl_ob ar ax hv hp0) (vl_ob ar ax hv hp0) (vl_sg ar ax hv z hp1) (vl_sg ar ax hv w hp1)
    (vl_op ar ax hv (sgT z) (sgT w) hp3) (vl_op ar ax hv z w hp2)

theorem n_m7 (x p q r : N) {k0 : H.W} (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b) :
    Fm.Tin ar (opT (sgT (sgT p)) (opT q r)) (i2T x) (H.suc (H.suc (H.suc (H.suc k0)))) v ↔ Fm.Tin ar (opT p r) x (H.suc (H.suc k0)) v := by
  have hp4 := hv.down hp5
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  exact (vs5 ar ax x 0 hv hp0 hp1 hp2 hp3 hp4 hp5).2 (Fm.vl ar (num (p)) k0 v) (Fm.vl ar (num (q)) k0 v) (Fm.vl ar (num (r)) k0 v) (Fm.vl ar (num (sgT p)) (H.suc k0) v)
    (Fm.vl ar (num (sgT (sgT p))) (H.suc (H.suc k0)) v) (Fm.vl ar (num (opT q r)) (H.suc (H.suc k0)) v) _ _ (vl_ob ar ax hv hp0) (vl_ob ar ax hv hp0)
    (vl_ob ar ax hv hp0) (vl_sg ar ax hv p hp1) (vl_sg ar ax hv (sgT p) hp2)
    (vl_op ar ax hv q r hp2) (vl_op ar ax hv (sgT (sgT p)) (opT q r) hp4) (vl_op ar ax hv p r hp2)

theorem n_m8 (x p q r : N) {k0 : H.W} (hp5 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc (H.suc k0))))) b) :
    Fm.Tin ar (opT (sgT (sgT p)) (opT q r)) (i3T x) (H.suc (H.suc (H.suc (H.suc k0)))) v ↔ Fm.Tin ar (opT p q) x (H.suc (H.suc k0)) v := by
  have hp4 := hv.down hp5
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  exact (vs6 ar ax x 0 hv hp0 hp1 hp2 hp3 hp4 hp5).2 (Fm.vl ar (num (p)) k0 v) (Fm.vl ar (num (q)) k0 v) (Fm.vl ar (num (r)) k0 v) (Fm.vl ar (num (sgT p)) (H.suc k0) v)
    (Fm.vl ar (num (sgT (sgT p))) (H.suc (H.suc k0)) v) (Fm.vl ar (num (opT q r)) (H.suc (H.suc k0)) v) _ _ (vl_ob ar ax hv hp0) (vl_ob ar ax hv hp0)
    (vl_ob ar ax hv hp0) (vl_sg ar ax hv p hp1) (vl_sg ar ax hv (sgT p) hp2)
    (vl_op ar ax hv q r hp2) (vl_op ar ax hv (sgT (sgT p)) (opT q r) hp4) (vl_op ar ax hv p q hp2)

theorem n_m9a (x p : N) {k0 : H.W} (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b)
    (h : Fm.Tin ar p (vcT x) (H.suc (H.suc k0)) v) :
    Fm.Teq ar p (opT (p1T p) (p2T p)) (H.suc (H.suc k0)) v ∧ Fm.Tin ar (p2T p) x k0 v := by
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  have l01 := plc_lt hv hp0 hp1
  have l12 := plc_lt hv hp1 hp2
  obtain ⟨q, r, hq, hr, hop, hel⟩ :=
    ((vs7 ar ax x 0 hv hp0 hp1 hp2 hp3).2 _ (vl_ob ar ax hv hp2)).mp h
  obtain ⟨hb1, r', hr', hop1⟩ := vs13 ar ax p 0 hv hp0 hp1 hp2 ⟨q, hq, r, hr, hop⟩
  obtain ⟨hb2, q', hq', hop2⟩ := vs14 ar ax p 0 hv hp0 hp1 hp2 ⟨r, hr, q, hq, hop⟩
  have e1 : (Fm.vl ar (num (p1T p)) k0 v) = q := (op_inj ax hb1 hr' hq hr hop1 hop).1
  have e2 : (Fm.vl ar (num (p2T p)) k0 v) = r := (op_inj ax hq' hb2 hq hr hop2 hop).2
  have hop3 := vl_op ar ax hv (p1T p) (p2T p) hp2
  refine ⟨?_, ?_⟩
  · unfold Teq
    rw [e1, e2] at hop3
    exact op_unique ax l12 l01 hop hop3
  · unfold Tin
    rw [e2]
    exact hel

theorem n_m9b (x p q r : N) {k0 : H.W} (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b)
    (h : Fm.Teq ar p (opT q r) (H.suc (H.suc k0)) v) (h' : Fm.Tin ar r x k0 v) : Fm.Tin ar p (vcT x) (H.suc (H.suc k0)) v := by
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  have hop := vl_op ar ax hv q r hp2
  unfold Teq at h
  rw [← h] at hop
  exact ((vs7 ar ax x 0 hv hp0 hp1 hp2 hp3).2 _ (vl_ob ar ax hv hp2)).mpr
    ⟨_, _, vl_ob ar ax hv hp0, vl_ob ar ax hv hp0, hop, h'⟩

theorem n_m10a (x p q : N) {k0 : H.W} (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (h : Fm.Tin ar p (tlT x) k0 v) : Fm.Tin ar (opT q (sgT p)) x (H.suc (H.suc (H.suc k0))) v := by
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  exact ((vs8 ar ax x 0 hv hp0 hp1 hp2 hp3 hp4).2 _ (vl_ob ar ax hv hp0)).mp h (Fm.vl ar (num (q)) (H.suc k0) v)
    (Fm.vl ar (num (sgT p)) (H.suc k0) v) _ (vl_ob ar ax hv hp1) (vl_sg ar ax hv p hp1) (vl_op ar ax hv q (sgT p) hp3)

theorem n_m10b (x p : N) {k0 : H.W} (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (h : Fm.Tin ar (opT (wtT p x) (sgT p)) x (H.suc (H.suc (H.suc k0))) v) : Fm.Tin ar p (tlT x) k0 v := by
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  have l01 := plc_lt hv hp0 hp1
  have l12 := plc_lt hv hp1 hp2
  have l23 := plc_lt hv hp2 hp3
  refine ((vs8 ar ax x 0 hv hp0 hp1 hp2 hp3 hp4).2 _ (vl_ob ar ax hv hp0)).mpr ?_
  intro q sp P hq hsp hP
  by_contra hnel
  obtain ⟨-, sp', P', hsp', hP', hnel'⟩ :=
    vs16 ar ax p x hv hp0 hp1 hp2 hp3 hp4 ⟨q, hq, sp, P, hsp, hP, hnel⟩
  have e1 := sg_unique ax l01 hsp' (vl_sg ar ax hv p hp1)
  rw [e1] at hP'
  have e2 := op_unique ax l23 l12 hP' (vl_op ar ax hv (wtT p x) (sgT p) hp3)
  rw [e2] at hnel'
  exact hnel' h

theorem n_m11 (x p q : N) {k0 : H.W} (hp3 : ∃ b, H.App v (H.suc (H.suc (H.suc k0))) b) :
    Fm.Tin ar (opT p q) (cvT x) (H.suc (H.suc k0)) v ↔ Fm.Tin ar (opT q p) x (H.suc (H.suc k0)) v := by
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  exact (vs9 ar ax x 0 hv hp0 hp1 hp2 hp3).2 (Fm.vl ar (num (p)) k0 v) (Fm.vl ar (num (q)) k0 v) _ _ (vl_ob ar ax hv hp0)
    (vl_ob ar ax hv hp0) (vl_op ar ax hv p q hp2) (vl_op ar ax hv q p hp2)

theorem n_m12a (p : N) {k0 : H.W} (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b)
    (h : Fm.Tin ar p c1T (H.suc k0) v) : Fm.Teq ar p (sgT (elT p)) (H.suc k0) v := by
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  obtain ⟨q, hq, hsg⟩ := ((vs10 ar ax 0 0 hv hp0 hp1 hp2).2 _ (vl_ob ar ax hv hp1)).mp h
  obtain ⟨-, hsg'⟩ := vs15 ar ax p 0 hv hp0 hp1 ⟨q, hq, hsg⟩
  exact sg_unique ax (plc_lt hv hp0 hp1) hsg' (vl_sg ar ax hv (elT p) hp1)

theorem n_m12b (p q : N) {k0 : H.W} (hp2 : ∃ b, H.App v (H.suc (H.suc k0)) b)
    (h : Fm.Teq ar p (sgT q) (H.suc k0) v) : Fm.Tin ar p c1T (H.suc k0) v := by
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  have hsg := vl_sg ar ax hv q hp1
  unfold Teq at h
  rw [← h] at hsg
  exact ((vs10 ar ax 0 0 hv hp0 hp1 hp2).2 _ (vl_ob ar ax hv hp1)).mpr
    ⟨_, vl_ob ar ax hv hp0, hsg⟩

theorem n_m13a (p q r : N) {k0 : H.W} (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (h : Fm.Tin ar (opT p q) sbT (H.suc (H.suc (H.suc k0))) v) (h' : Fm.Tin ar r p k0 v) : Fm.Tin ar r q k0 v := by
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  exact ((vs11 ar ax 0 0 hv hp0 hp1 hp2 hp3 hp4).2 (Fm.vl ar (num (p)) (H.suc k0) v) (Fm.vl ar (num (q)) (H.suc k0) v) _ (vl_ob ar ax hv hp1)
    (vl_ob ar ax hv hp1) (vl_op ar ax hv p q hp3)).mp h _ (vl_ob ar ax hv hp0) h'

theorem n_m13b (p q : N) {k0 : H.W} (hp4 : ∃ b, H.App v (H.suc (H.suc (H.suc (H.suc k0)))) b)
    (h : Fm.Tin ar (wsT p q) p k0 v → Fm.Tin ar (wsT p q) q k0 v) :
    Fm.Tin ar (opT p q) sbT (H.suc (H.suc (H.suc k0))) v := by
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  refine ((vs11 ar ax 0 0 hv hp0 hp1 hp2 hp3 hp4).2 (Fm.vl ar (num (p)) (H.suc k0) v) (Fm.vl ar (num (q)) (H.suc k0) v) _ (vl_ob ar ax hv hp1)
    (vl_ob ar ax hv hp1) (vl_op ar ax hv p q hp3)).mpr ?_
  intro r hr hrp
  by_contra hrq
  obtain ⟨-, h1, h2⟩ := vs17 ar ax p q hv hp0 hp1 ⟨r, hr, hrp, hrq⟩
  exact h2 (h h1)

end FlatM

/-! ## Phase 2 (A6): locality

The value of a term at a position of a placement depends only on the placement near the
position. `Bis v w I` is a family of correspondences `I d` between positions of `v` and `w`,
"corresponding and at distance at least `d` from the ends"; the value of the term `t` is the
same at positions that correspond at the distance `5 t + 5`. The part `tn_mono` is generated
by `gen/gen49.py`. -/

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- The selection conditions only look at the levels around the position. -/
theorem tn_mono {v w k k' : H.W} (h0 : ∀ a, H.L0 v k a → H.L0 w k' a)
    (hm1 : ∀ a, H.Lm1 v k a → H.Lm1 w k' a) (hm2 : ∀ a, H.Lm2 v k a → H.Lm2 w k' a)
    (hm3 : ∀ a, H.Lm3 v k a → H.Lm3 w k' a) (hm4 : ∀ a, H.Lm4 v k a → H.Lm4 w k' a)
    (hm5 : ∀ a, H.Lm5 v k a → H.Lm5 w k' a) (hp1 : ∀ a, H.Lp1 v k a → H.Lp1 w k' a)
    (hp2 : ∀ a, H.Lp2 v k a → H.Lp2 w k' a) (hp3 : ∀ a, H.Lp3 v k a → H.Lp3 w k' a) :
    ∀ (i : ℕ) (y c1 c2 : H.W), Fm.Tn i y c1 c2 k v → Fm.Tn i y c1 c2 k' w
  | 0, _, _, _, ⟨a, a1, h_a, h_a1, hb⟩ => ⟨a, a1, h0 _ h_a, hm1 _ h_a1, hb⟩
  | 1, _, _, _, ⟨a, a1, h_a, h_a1, hb⟩ => ⟨a, a1, h0 _ h_a, hm1 _ h_a1, hb⟩
  | 2, _, _, _, ⟨a, a1, h_a, h_a1, hb⟩ => ⟨a, a1, h0 _ h_a, hm1 _ h_a1, hb⟩
  | 3, _, _, _, ⟨a, a1, h_a, h_a1, hb⟩ => ⟨a, a1, h0 _ h_a, hm1 _ h_a1, hb⟩
  | 4, _, _, _, ⟨a, a1, a2, a3, a4, h_a, h_a1, h_a2, h_a3, h_a4, hb⟩ => ⟨a, a1, a2, a3, a4, h0 _ h_a, hm1 _ h_a1, hm2 _ h_a2, hm3 _ h_a3, hm4 _ h_a4, hb⟩
  | 5, _, _, _, ⟨a, a1, a2, a3, a4, a5, h_a, h_a1, h_a2, h_a3, h_a4, h_a5, hb⟩ => ⟨a, a1, a2, a3, a4, a5, h0 _ h_a, hm1 _ h_a1, hm2 _ h_a2, hm3 _ h_a3, hm4 _ h_a4, hm5 _ h_a5, hb⟩
  | 6, _, _, _, ⟨a, a1, a2, a3, a4, a5, h_a, h_a1, h_a2, h_a3, h_a4, h_a5, hb⟩ => ⟨a, a1, a2, a3, a4, a5, h0 _ h_a, hm1 _ h_a1, hm2 _ h_a2, hm3 _ h_a3, hm4 _ h_a4, hm5 _ h_a5, hb⟩
  | 7, _, _, _, ⟨a, a1, a2, a3, h_a, h_a1, h_a2, h_a3, hb⟩ => ⟨a, a1, a2, a3, h0 _ h_a, hm1 _ h_a1, hm2 _ h_a2, hm3 _ h_a3, hb⟩
  | 8, _, _, _, ⟨a, a1, u1, u2, u3, h_a, h_a1, h_u1, h_u2, h_u3, hb⟩ => ⟨a, a1, u1, u2, u3, h0 _ h_a, hm1 _ h_a1, hp1 _ h_u1, hp2 _ h_u2, hp3 _ h_u3, hb⟩
  | 9, _, _, _, ⟨a, a1, a2, a3, h_a, h_a1, h_a2, h_a3, hb⟩ => ⟨a, a1, a2, a3, h0 _ h_a, hm1 _ h_a1, hm2 _ h_a2, hm3 _ h_a3, hb⟩
  | 10, _, _, _, ⟨a, a1, a2, h_a, h_a1, h_a2, hb⟩ => ⟨a, a1, a2, h0 _ h_a, hm1 _ h_a1, hm2 _ h_a2, hb⟩
  | 11, _, _, _, ⟨a, a1, a2, a3, a4, h_a, h_a1, h_a2, h_a3, h_a4, hb⟩ => ⟨a, a1, a2, a3, a4, h0 _ h_a, hm1 _ h_a1, hm2 _ h_a2, hm3 _ h_a3, hm4 _ h_a4, hb⟩
  | 12, _, _, _, ⟨a, u1, h_a, h_u1, hb⟩ => ⟨a, u1, h0 _ h_a, hp1 _ h_u1, hb⟩
  | 13, _, _, _, ⟨a, u1, u2, h_a, h_u1, h_u2, hb⟩ => ⟨a, u1, u2, h0 _ h_a, hp1 _ h_u1, hp2 _ h_u2, hb⟩
  | 14, _, _, _, ⟨a, u1, u2, h_a, h_u1, h_u2, hb⟩ => ⟨a, u1, u2, h0 _ h_a, hp1 _ h_u1, hp2 _ h_u2, hb⟩
  | 15, _, _, _, ⟨a, u1, h_a, h_u1, hb⟩ => ⟨a, u1, h0 _ h_a, hp1 _ h_u1, hb⟩
  | 16, _, _, _, ⟨a, a1, u1, u2, u3, h_a, h_a1, h_u1, h_u2, h_u3, hb⟩ => ⟨a, a1, u1, u2, u3, h0 _ h_a, hm1 _ h_a1, hp1 _ h_u1, hp2 _ h_u2, hp3 _ h_u3, hb⟩
  | 17, _, _, _, ⟨a, u1, h_a, h_u1, hb⟩ => ⟨a, u1, h0 _ h_a, hp1 _ h_u1, hb⟩
  | (_ + 18), _, _, _, h => h.elim

/-- A family of correspondences between the positions of two placements. -/
structure Bis (v w : H.W) (I : N → H.W → H.W → Prop) : Prop where
  app : ∀ d k k', I d k k' → ∀ a, H.App v k a ↔ H.App w k' a
  up : ∀ d k k', I (d + 1) k k' → I d (H.suc k) (H.suc k')
  dn : ∀ d k k' k1, I (d + 1) k k' → k = H.suc k1 → ∃ k1', k' = H.suc k1' ∧ I d k1 k1'
  dn' : ∀ d k k' k1', I (d + 1) k k' → k' = H.suc k1' → ∃ k1, k = H.suc k1 ∧ I d k1 k1'
  mono : ∀ d c k k', I (d + c) k k' → I d k k'

namespace Bis

variable {v w : H.W} {I : N → H.W → H.W → Prop}

theorem symm (h : Bis v w I) : Bis w v (fun d k k' => I d k' k) where
  app := fun d k k' hI a => (h.app d k' k hI a).symm
  up := fun d k k' hI => h.up d k' k hI
  dn := fun d k k' k1 hI e => h.dn' d k' k k1 hI e
  dn' := fun d k k' k1' hI e => h.dn d k' k k1' hI e
  mono := fun d c k k' hI => h.mono d c k' k hI

theorem sh (h : Bis v w I) : ∀ (o : ℕ) (d : N) (k k' k1 : H.W), I (d + 3) k k' → H.Sh o k k1 →
    ∃ k1', H.Sh o k' k1' ∧ I d k1 k1'
  | 0, d, k, k', k1, hI, hs => ⟨k', rfl, by
      rw [show k1 = k from hs]
      exact h.mono d 3 k k' hI⟩
  | 1, d, k, k', k1, hI, hs => by
      obtain ⟨k1', e, hI'⟩ := h.dn (d + 2) k k' k1 (by
        rw [show d + 2 + 1 = d + 3 from by ring]
        exact hI) hs
      exact ⟨k1', e, h.mono d 2 _ _ hI'⟩
  | 2, d, k, k', k1, hI, hs => by
      obtain ⟨ka', e, hI'⟩ := h.dn (d + 1 + 1) k k' (H.suc k1) (by
        rw [show d + 1 + 1 + 1 = d + 3 from by ring]
        exact hI) hs
      obtain ⟨k1', e', hI''⟩ := h.dn (d + 1) (H.suc k1) ka' k1 hI' rfl
      refine ⟨k1', ?_, h.mono d 1 _ _ hI''⟩
      show k' = H.suc (H.suc k1')
      rw [e, e']
  | 3, d, k, k', k1, hI, hs => by
      refine ⟨H.suc k', rfl, ?_⟩
      rw [show k1 = H.suc k from hs]
      exact h.mono d 2 _ _ (h.up (d + 2) k k' (by
        rw [show d + 2 + 1 = d + 3 from by ring]
        exact hI))
  | 4, d, k, k', k1, hI, hs => by
      refine ⟨H.suc (H.suc k'), rfl, ?_⟩
      rw [show k1 = H.suc (H.suc k) from hs]
      exact h.mono d 1 _ _ (h.up (d + 1) _ _ (h.up (d + 1 + 1) k k' (by
        rw [show d + 1 + 1 + 1 = d + 3 from by ring]
        exact hI)))
  | 5, d, k, k', k1, hI, hs => by
      refine ⟨H.suc (H.suc (H.suc k')), rfl, ?_⟩
      rw [show k1 = H.suc (H.suc (H.suc k)) from hs]
      exact h.up d _ _ (h.up (d + 1) _ _ (h.up (d + 1 + 1) k k' (by
        rw [show d + 1 + 1 + 1 = d + 3 from by ring]
        exact hI)))
  | (_ + 6), _, _, _, _, _, hs => hs.elim

theorem lm1 (h : Bis v w I) {d : N} {k k' a : H.W} (hI : I (d + 1) k k') :
    H.Lm1 v k a → H.Lm1 w k' a := fun ⟨k1, e, ha⟩ =>
  let ⟨k1', e', hI'⟩ := h.dn d k k' k1 hI e
  ⟨k1', e', (h.app d _ _ hI' a).mp ha⟩

theorem lm2 (h : Bis v w I) {d : N} {k k' a : H.W} (hI : I (d + 1 + 1) k k') :
    H.Lm2 v k a → H.Lm2 w k' a := fun ⟨k1, e, ha⟩ =>
  let ⟨k1', e', hI'⟩ := h.dn (d + 1) k k' k1 hI e
  ⟨k1', e', h.lm1 hI' ha⟩

theorem lm3 (h : Bis v w I) {d : N} {k k' a : H.W} (hI : I (d + 1 + 1 + 1) k k') :
    H.Lm3 v k a → H.Lm3 w k' a := fun ⟨k1, e, ha⟩ =>
  let ⟨k1', e', hI'⟩ := h.dn (d + 1 + 1) k k' k1 hI e
  ⟨k1', e', h.lm2 hI' ha⟩

theorem lm4 (h : Bis v w I) {d : N} {k k' a : H.W} (hI : I (d + 1 + 1 + 1 + 1) k k') :
    H.Lm4 v k a → H.Lm4 w k' a := fun ⟨k1, e, ha⟩ =>
  let ⟨k1', e', hI'⟩ := h.dn (d + 1 + 1 + 1) k k' k1 hI e
  ⟨k1', e', h.lm3 hI' ha⟩

theorem lm5 (h : Bis v w I) {d : N} {k k' a : H.W} (hI : I (d + 1 + 1 + 1 + 1 + 1) k k') :
    H.Lm5 v k a → H.Lm5 w k' a := fun ⟨k1, e, ha⟩ =>
  let ⟨k1', e', hI'⟩ := h.dn (d + 1 + 1 + 1 + 1) k k' k1 hI e
  ⟨k1', e', h.lm4 hI' ha⟩

/-- The selection conditions agree at positions that correspond at the distance `5`. -/
theorem tn (h : Bis v w I) {k k' : H.W} (hI : I 5 k k') (i : ℕ) (y c1 c2 : H.W) :
    Fm.Tn i y c1 c2 k v → Fm.Tn i y c1 c2 k' w := by
  have m : ∀ d c : N, d + c = 5 → I d k k' := fun d c e => h.mono d c k k' (by
    rw [e]
    exact hI)
  exact tn_mono (fun a => (h.app 0 _ _ (m 0 5 (by ring)) a).mp)
    (fun a => h.lm1 (m (0 + 1) 4 (by ring)))
    (fun a => h.lm2 (m (0 + 1 + 1) 3 (by ring)))
    (fun a => h.lm3 (m (0 + 1 + 1 + 1) 2 (by ring)))
    (fun a => h.lm4 (m (0 + 1 + 1 + 1 + 1) 1 (by ring)))
    (fun a => h.lm5 (m (0 + 1 + 1 + 1 + 1 + 1) 0 (by ring)))
    (fun a => (h.app 0 _ _ (h.up 0 _ _ (m (0 + 1) 4 (by ring))) a).mp)
    (fun a => (h.app 0 _ _ (h.up 0 _ _ (h.up (0 + 1) _ _ (m (0 + 1 + 1) 3 (by ring)))) a).mp)
    (fun a => (h.app 0 _ _ (h.up 0 _ _ (h.up (0 + 1) _ _ (h.up (0 + 1 + 1) _ _
      (m (0 + 1 + 1 + 1) 2 (by ring))))) a).mp) i y c1 c2

theorem th (h : Bis v w I) {k k' : H.W} (hI : I 5 k k') (f y c1 c2 : H.W) :
    Fm.Th num f y (H.op (H.op c1 c2) (H.op k v)) ↔
      Fm.Th num f y (H.op (H.op c1 c2) (H.op k' w)) := by
  rw [Fm.th_iff num, Fm.th_iff num]
  constructor
  · rintro ⟨i, hi, hf, hT⟩
    exact ⟨i, hi, hf, h.tn hI i y c1 c2 hT⟩
  · rintro ⟨i, hi, hf, hT⟩
    exact ⟨i, hi, hf, h.symm.tn hI i y c1 c2 hT⟩

theorem args (ar : H.Arith E num) (h : Bis v w I) {d : N} {n k k' f n1 n2 k1 k2 : H.W}
    (hI : I (d + 3) k k') (ha : Args ar v n k f n1 n2 k1 k2) :
    ∃ k1' k2', Args ar w n k' f n1 n2 k1' k2' ∧ I d k1 k1' ∧ I d k2 k2' := by
  obtain ⟨hdec, ho1, ho2, ⟨b1, hb1⟩, ⟨b2, hb2⟩⟩ := ha
  obtain ⟨i, hi, hf, hs1⟩ := (off1_iff num).mp ho1
  obtain ⟨i', hi', hf', hs2⟩ := (off2_iff num).mp ho2
  obtain ⟨k1', hs1', hI1⟩ := h.sh _ d k k' k1 hI hs1
  obtain ⟨k2', hs2', hI2⟩ := h.sh _ d k k' k2 hI hs2
  exact ⟨k1', k2', ⟨hdec, (off1_iff num).mpr ⟨i, hi, hf, hs1'⟩,
    (off2_iff num).mpr ⟨i', hi', hf', hs2'⟩, ⟨b1, (h.app d _ _ hI1 b1).mp hb1⟩,
    ⟨b2, (h.app d _ _ hI2 b2).mp hb2⟩⟩, hI1, hI2⟩

end Bis

theorem pick_congr {f a c p p' : H.W} (hth : ∀ y, Fm.Th num f y p ↔ Fm.Th num f y p') :
    Fm.Pick num f a c p → Fm.Pick num f a c p' := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨(hth c).mp h1, fun y hy hy' => h2 y hy ((hth y).mpr hy')⟩
  · exact Or.inr ⟨fun ⟨y, hy⟩ => h1 ⟨y, (hth y).mpr hy⟩, h2⟩

/-- One step of the induction for locality, in one direction. -/
theorem loc_step (ar : H.Arith E num) {v w : H.W} {I : N → H.W → H.W → Prop} (h : Bis v w I)
    (t : N)
    (ih : ∀ x : N, x + 1 ≤ t → ∀ k k' c, I (5 * x + 5) k k' →
      (Fm.Val ar (num x) k v c ↔ Fm.Val ar (num x) k' w c))
    {k k' c : H.W} (hI : I (5 * t + 5) k k') (hval : Fm.Val ar (num t) k v c) :
    Fm.Val ar (num t) k' w c := by
  obtain ⟨a, ha, hcase⟩ := (Fm.val_iff ar).mp hval
  have hI5 : I 5 k k' := h.mono 5 (5 * t) k k' (by
    rw [show (5 : N) + 5 * t = 5 * t + 5 from by ring]
    exact hI)
  have hI3 : I (0 + 3) k k' := h.mono (0 + 3) (5 * t + 2) k k' (by
    rw [show (0 : N) + 3 + (5 * t + 2) = 5 * t + 5 from by ring]
    exact hI)
  refine (Fm.val_iff ar).mpr ⟨a, (h.app _ _ _ hI a).mp ha, ?_⟩
  rcases hcase with ⟨f, n1, n2, k1, k2, c1, c2, hargs, hv1, hv2, hpick⟩ | ⟨hno, hleast⟩
  · obtain ⟨f', x, y, rfl, rfl, rfl, et⟩ := ar.dec_iff.mp hargs.1
    have et' : t = npair f' (npair x y) + 1 := ar.num_inj et
    have hx : x + 1 ≤ t := by
      rw [et']
      exact ar.nf.add_le_add_r (le_trans (ar.le_npair_left x y) (ar.le_npair_right f' _)) 1
    have hy : y + 1 ≤ t := by
      rw [et']
      exact ar.nf.add_le_add_r (le_trans (ar.le_npair_right x y) (ar.le_npair_right f' _)) 1
    obtain ⟨s, hs⟩ := (ar.nf.le_iff _ _).mp hx
    obtain ⟨s', hs'⟩ := (ar.nf.le_iff _ _).mp hy
    have hIx : I (5 * x + 5 + 3) k k' := h.mono _ (2 + 5 * s) k k' (by
      rw [show 5 * x + 5 + 3 + (2 + 5 * s) = 5 * (x + 1 + s) + 5 from by ring, hs]
      exact hI)
    have hIy : I (5 * y + 5 + 3) k k' := h.mono _ (2 + 5 * s') k k' (by
      rw [show 5 * y + 5 + 3 + (2 + 5 * s') = 5 * (y + 1 + s') + 5 from by ring, hs']
      exact hI)
    obtain ⟨k1', k2', hargs', hI1, -⟩ := h.args ar hIx hargs
    obtain ⟨k1'', k2'', hargs'', -, hI2⟩ := h.args ar hIy hargs
    obtain ⟨-, -, -, e1, e2⟩ := args_unique ar hargs' hargs''
    subst e1 e2
    exact Or.inl ⟨_, _, _, k1', k2', c1, c2, hargs', (ih x hx _ _ _ hI1).mp hv1,
      (ih y hy _ _ _ hI2).mp hv2, pick_congr (fun y => h.th hI5 _ y c1 c2) hpick⟩
  · refine Or.inr ⟨fun ⟨f, n1, n2, k1', k2', hargs'⟩ => hno ?_, hleast⟩
    obtain ⟨k1, k2, hargs, -, -⟩ := h.symm.args ar (d := 0) hI3 hargs'
    exact ⟨f, n1, n2, k1, k2, hargs⟩

end FlatM

/-! ## Phase 2 (A6, continued): locality for a segment of a placement -/

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- The position `m + j` of one placement and the position `j` of another correspond at the
distance `d` if `j` is at distance at least `d` from both ends of `[0, W)`. -/
def Iseg (num : N → H.W) (m W : N) (d : N) (k k' : H.W) : Prop :=
  ∃ j : N, d ≤ j ∧ j + d + 1 ≤ W ∧ k = num (m + j) ∧ k' = num j

theorem bis_seg (ar : H.Arith E num) {v w : H.W} {m W : N}
    (hseg : ∀ j : N, j + 1 ≤ W → ∀ b, H.App v (num (m + j)) b ↔ H.App w (num j) b) :
    Bis v w (Iseg num m W) where
  app := by
    rintro d k k' ⟨j, -, h2, rfl, rfl⟩ a
    exact hseg j (le_trans ((ar.nf.le_iff _ _).mpr ⟨d, by ring⟩) h2) a
  up := by
    rintro d k k' ⟨j, h1, h2, rfl, rfl⟩
    refine ⟨j + 1, le_trans (ar.nf.le_add d 1) (le_trans h1 (ar.nf.le_add j 1)), ?_, ?_, ?_⟩
    · rw [show j + 1 + d + 1 = j + (d + 1) + 1 from by ring]
      exact h2
    · rw [← ar.iso.succ, add_assoc]
    · rw [← ar.iso.succ]
  dn := by
    rintro d k k' k1 ⟨j, h1, h2, rfl, rfl⟩ e
    obtain ⟨s, rfl⟩ := (ar.nf.le_iff _ _).mp h1
    have e1 : num (m + (d + 1 + s)) = H.suc (num (m + (d + s))) := by
      rw [← ar.iso.succ]
      congr 1
      ring
    have ek : k1 = num (m + (d + s)) := H.suc_inj (e.symm.trans e1)
    subst ek
    refine ⟨num (d + s), ?_, d + s, ar.nf.le_add d s, ?_, rfl, rfl⟩
    · rw [← ar.iso.succ]
      congr 1
      ring
    · exact le_trans ((ar.nf.le_iff _ _).mpr ⟨2, by ring⟩) h2
  dn' := by
    rintro d k k' k1' ⟨j, h1, h2, rfl, rfl⟩ e
    obtain ⟨s, rfl⟩ := (ar.nf.le_iff _ _).mp h1
    have e1 : num (d + 1 + s) = H.suc (num (d + s)) := by
      rw [← ar.iso.succ]
      congr 1
      ring
    have ek : k1' = num (d + s) := H.suc_inj (e.symm.trans e1)
    subst ek
    refine ⟨num (m + (d + s)), ?_, d + s, ar.nf.le_add d s, ?_, rfl, rfl⟩
    · rw [← ar.iso.succ]
      congr 1
      ring
    · exact le_trans ((ar.nf.le_iff _ _).mpr ⟨2, by ring⟩) h2
  mono := by
    rintro d c k k' ⟨j, h1, h2, rfl, rfl⟩
    exact ⟨j, le_trans (ar.nf.le_add d c) h1,
      le_trans ((ar.nf.le_iff _ _).mpr ⟨c, by ring⟩) h2, rfl, rfl⟩

/-- `r = 5 n + 5`, in the host. -/
def Rad (ar : H.Arith E num) (n r : H.W) : Prop := ∃ x, ar.Mu (num 5) n x ∧ ar.Ad x (num 5) r

theorem rad_iff (ar : H.Arith E num) {t : N} {r : H.W} :
    Rad ar (num t) r ↔ r = num (5 * t + 5) := by
  constructor
  · rintro ⟨x, h1, h2⟩
    rw [ar.mu_iff.mp h1] at h2
    exact ar.ad_iff.mp h2
  · rintro rfl
    exact ⟨_, ar.mu_iff.mpr rfl, ar.ad_iff.mpr rfl⟩

/-- The statement of locality for the term `n`, in the language of the host. -/
def LocP (Fm : FlatM H) (ar : H.Arith E num) (v w mm WW : H.W) (n : H.W) : Prop :=
  n ∈ H.om → ∀ r j k c, Rad ar n r → j ∈ H.om → (r ∈ j ∨ r = j) →
    (∃ s, ar.Ad j r s ∧ (H.suc s ∈ WW ∨ H.suc s = WW)) → ar.Ad mm j k →
    (Fm.Vl ar n c (H.op k v) ↔ Fm.Vl ar n c (H.op j w))

theorem locP_iff (ar : H.Arith E num) {v w : H.W} {m W t : N} :
    LocP Fm ar v w (num m) (num W) (num t) ↔
      ∀ k k' c, Iseg num m W (5 * t + 5) k k' →
        (Fm.Val ar (num t) k v c ↔ Fm.Val ar (num t) k' w c) := by
  constructor
  · rintro hP k k' c ⟨j, h1, h2, rfl, rfl⟩
    exact hP (ar.num_om t) (num (5 * t + 5)) (num j) (num (m + j)) c ((rad_iff ar).mpr rfl)
      (ar.num_om j) (ar.num_le.mpr h1)
      ⟨num (j + (5 * t + 5)), ar.ad_iff.mpr rfl, by
        rw [← ar.iso.succ]
        exact ar.num_le.mpr h2⟩ (ar.ad_iff.mpr rfl)
  · intro hN _ r j k c hr hj h1 h2 hk
    obtain ⟨j', rfl⟩ := ar.of_om hj
    rw [rad_iff ar] at hr
    subst hr
    obtain ⟨s, hs, h3⟩ := h2
    rw [ar.ad_iff.mp hs, ← ar.iso.succ] at h3
    rw [ar.ad_iff.mp hk]
    exact hN _ _ c ⟨j', ar.num_le.mp h1, ar.num_le.mp h3, rfl, rfl⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **Locality.** If `w` is the segment of `v` that starts at `m` and has the length `W`, then
the term `t` has the same value at the position `m + j` of `v` and at the position `j` of `w`,
provided `j` is at distance at least `5 t + 5` from both ends of the segment. -/
theorem loc (ar : H.Arith E num) {v w : H.W} {m W : N}
    (hseg : ∀ j : N, j + 1 ≤ W → ∀ b, H.App v (num (m + j)) b ↔ H.App w (num j) b) (t : N) :
    ∀ k k' c, Iseg num m W (5 * t + 5) k k' →
      (Fm.Val ar (num t) k v c ↔ Fm.Val ar (num t) k' w c) := by
  have hV := Fm.def_vl ar
  have hA := ar.def_Ad
  have hM := ar.def_Mu
  have hbis := bis_seg ar hseg
  have key : ∀ n, LocP Fm ar v w (num m) (num W) n := by
    refine H.lt_ind (LocP Fm ar v w (num m) (num W)) (by hdef) ?_
    intro n ih
    by_cases hn : n ∈ H.om
    · obtain ⟨t, rfl⟩ := ar.of_om hn
      have ihN : ∀ x : N, x + 1 ≤ t → ∀ k k' c, Iseg num m W (5 * x + 5) k k' →
          (Fm.Val ar (num x) k v c ↔ Fm.Val ar (num x) k' w c) :=
        fun x hx => (locP_iff ar).mp (ih (num x) (H.mem_lt _ _ (ar.num_mem.mpr hx)))
      exact (locP_iff ar).mpr fun k k' c hI =>
        ⟨loc_step ar hbis t ihN hI,
          loc_step ar hbis.symm t (fun x hx k k' c hI' => (ihN x hx k' k c hI').symm) hI⟩
    · exact fun hn' => (hn hn').elim
  exact (locP_iff ar).mp (key (num t))

end FlatM

/-! ## Phase 2 (A7, fourth part): the step of Ramsey's theorem as a statement about `Ram` -/

namespace Host

variable {H : Host}

section ramstep

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- Exponent zero: every sequence is homogeneous for sets of no values. -/
theorem ram_zero (ar : H.Arith E num) (q : H.W) : H.Ram (num 0) q q := by
  intro c F hF
  have hemp : ∀ {B : H.W}, H.Card B (num 0) → B = H.emp := fun {B} ⟨s, hs, hsm⟩ =>
    H.eq_emp fun z hz => by
      obtain ⟨i, hi⟩ := (hsm z).mp hz
      have := hs.dom hi
      rw [ar.iso.zero] at this
      exact H.not_mem_emp i this
  exact ⟨F, hF, fun i a h => ⟨i, h⟩, fun B B' hB hB' _ _ => by rw [hemp hB, hemp hB']⟩

/-- **The step of Ramsey's theorem.** (Copied from the proof of `ramsey`.) -/
theorem ram_step (ar : H.Arith E num) {r Q0 l : N} {q : H.W} (hram : H.Ram (num r) q (num Q0))
    (hl : rstep E Q0 ≤ l) : H.Ram (num (r + 1)) q (num l) := by
    have hdi := H.def_incSeq
    have hdc := H.def_card
    intro c F hF
    obtain ⟨A, hA, hAF, hph⟩ := H.exists_prehom ar c (n := Q0 + 1) hF hl
    have hlastdom : num Q0 ∈ num (Q0 + 1) := ar.num_mem.mpr (le_refl _)
    obtain ⟨last, hlast⟩ := hA.tot hlastdom
    have hA' := hA.res (ar.num_om Q0) (ar.num_sub (ar.nf.le_add Q0 1))
    obtain ⟨c1, hc1⟩ := H.sep' c (fun B => last ∈ B) (by hdef)
    obtain ⟨c', hc'⟩ := H.repl' c1 (fun Bp B => ∀ z, z ∈ B ↔ z ∈ Bp ∧ z ≠ last) (by hdef)
      (fun u _ v v' h h' => H.ext' fun z => (h z).trans (h' z).symm)
    have hc'iff : ∀ B, ¬ last ∈ B → (B ∈ c' ↔ H.bun B (H.sg last) ∈ c) := by
      intro B hB
      rw [hc' B]
      constructor
      · rintro ⟨Bp, hBp, hrel⟩
        obtain ⟨hBpc, hl⟩ := (hc1 Bp).mp hBp
        have e : H.bun B (H.sg last) = Bp := H.ext' fun z => by
          rw [H.mem_bun, H.mem_sg, hrel z]
          constructor
          · rintro (h | h)
            · exact h.1
            · rw [h]
              exact hl
          · intro h
            by_cases e : z = last
            · exact Or.inr e
            · exact Or.inl ⟨h, e⟩
        rw [e]
        exact hBpc
      · intro h
        refine ⟨H.bun B (H.sg last),
          (hc1 _).mpr ⟨h, H.mem_bun.mpr (Or.inr (H.mem_sg.mpr rfl))⟩, fun z => ?_⟩
        rw [H.mem_bun, H.mem_sg]
        constructor
        · intro hz
          exact ⟨Or.inl hz, fun e => hB (e ▸ hz)⟩
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact (h2 h1).elim
    obtain ⟨g, hg, hgA', hhom⟩ := hram c' (H.res A (num Q0)) hA'
    have hgl : ∀ i a, H.App g i a → (∃ j, H.App A j a) ∧ a ∈ last := fun i a h => by
      obtain ⟨j, hj⟩ := hgA' i a h
      obtain ⟨hjd, hja⟩ := H.app_res.mp hj
      exact ⟨⟨j, hja⟩, hA.2.2.2 j (num Q0) a last hja hlast hjd⟩
    refine ⟨g, hg, fun i a h => ?_, ?_⟩
    · obtain ⟨⟨j, hj⟩, -⟩ := hgl i a h
      exact hAF j a hj
    have key : ∀ B, H.Card B (num (r + 1)) → H.SubV B g →
        ∃ B0, H.Card B0 (num r) ∧ H.SubV B0 g ∧ (B ∈ c ↔ B0 ∈ c') := by
      rintro B ⟨s, hs, hsm⟩ hBg
      have hrd : num r ∈ num (r + 1) := ar.num_mem.mpr (le_refl _)
      obtain ⟨x, hx⟩ := hs.tot hrd
      have hs0 := hs.res (ar.num_om r) (ar.num_sub (ar.nf.le_add r 1))
      obtain ⟨B0, hB0⟩ := H.sep' B (fun z => z ≠ x) (by hdef)
      have hB0m : ∀ z, z ∈ B0 ↔ ∃ i, H.App (H.res s (num r)) i z := by
        intro z
        rw [hB0 z, hsm z]
        constructor
        · rintro ⟨⟨i, hi⟩, hne⟩
          have hid := hs.dom hi
          rw [ar.iso.succ] at hid
          rcases H.mem_suc.mp hid with h | h
          · exact ⟨i, H.app_res.mpr ⟨h, hi⟩⟩
          · rw [h] at hi
            exact (hne (hs.fn hi hx)).elim
        · rintro ⟨i, hi⟩
          obtain ⟨hid, hi'⟩ := H.app_res.mp hi
          refine ⟨⟨i, hi'⟩, fun e => ?_⟩
          rw [e] at hi'
          exact H.mem_irrefl x (hs.2.2.2 i (num r) x x hi' hx hid)
      have hxB : x ∈ B := (hsm x).mpr ⟨_, hx⟩
      have hB0g : H.SubV B0 g := fun b hb => hBg b ((hB0 b).mp hb).1
      have hbel : H.Below B0 x := fun b hb => by
        obtain ⟨i, hi⟩ := (hB0m b).mp hb
        obtain ⟨hid, hi'⟩ := H.app_res.mp hi
        exact hs.2.2.2 i (num r) b x hi' hx hid
      have eB : B = H.bun B0 (H.sg x) := H.ext' fun z => by
        rw [H.mem_bun, H.mem_sg, hB0 z]
        constructor
        · intro h
          by_cases e : z = x
          · exact Or.inr e
          · exact Or.inl ⟨h, e⟩
        · rintro (h | h)
          · exact h.1
          · rw [h]
            exact hxB
      obtain ⟨jx, hjx⟩ := hBg x hxB
      obtain ⟨⟨kx, hkx⟩, hxl⟩ := hgl jx x hjx
      have hB0A : H.SubV B0 A := fun b hb => by
        obtain ⟨j, hj⟩ := hB0g b hb
        exact (hgl j b hj).1
      have hbl : H.Below B0 last := fun b hb => by
        obtain ⟨j, hj⟩ := hB0g b hb
        exact (hgl j b hj).2
      have hnl : ¬ last ∈ B0 := fun h => H.mem_irrefl last (hbl last h)
      refine ⟨B0, ⟨_, hs0, hB0m⟩, hB0g, ?_⟩
      rw [eB, hc'iff B0 hnl]
      exact hph B0 x last kx (num Q0) hB0A hkx hlast hbel hbl
    intro B B' hB hB' hBg hB'g
    obtain ⟨B0, h1, h2, h3⟩ := key B hB hBg
    obtain ⟨B0', h1', h2', h3'⟩ := key B' hB' hB'g
    rw [h3, h3']
    exact hhom B0 B0' h1 h1' h2 h2'

end ramstep

end Host

/-! ## Phase 2 (A7–A8): truth of atoms, and deciding one more atom along a sequence of levels -/

/-- The code of the atom `t ∈ t'`. -/
def aIn {N : Type} [CommSemiring N] (t t' : N) : N := npair t t' + npair t t'

/-- The code of the atom `t = t'`. -/
def aEq {N : Type} [CommSemiring N] (t t' : N) : N := npair t t' + npair t t' + 1

namespace NFacts

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} (nf : NFacts N E)
include nf

theorem double_inj {a b : N} (h : a + a = b + b) : a = b := by
  have key : ∀ a b : N, a ≤ b → a + a = b + b → a = b := by
    intro a b hab h
    obtain ⟨c, rfl⟩ := (nf.le_iff _ _).mp hab
    have h0 : 0 = c + c := nf.cancel 0 (c + c) (a + a) (by
      calc 0 + (a + a) = a + c + (a + c) := by rw [zero_add]; exact h
        _ = c + c + (a + a) := by ring)
    have hc : c = 0 := le_antisymm (by rw [h0]; exact nf.le_add c c) (nf.zero_le c)
    rw [hc, add_zero]
  rcases nf.total a b with h1 | h1
  · exact key a b h1 h
  · exact (key b a h1 h.symm).symm

theorem double_ne {a b : N} (h : a + a = b + b + 1) : False := by
  rcases nf.le_or_succ_le a b with h1 | h1
  · have h2 : a + a ≤ b + b := le_trans (nf.add_le_add_r h1 a) (nf.add_le_add_l h1 b)
    rw [h] at h2
    exact nf.not_succ_le _ h2
  · have h2 : b + 1 + (b + 1) ≤ a + a :=
      le_trans (nf.add_le_add_r h1 (b + 1)) (nf.add_le_add_l h1 a)
    rw [h, show b + 1 + (b + 1) = b + b + 1 + 1 from by ring] at h2
    exact nf.not_succ_le _ h2

theorem le_aIn_left (t t' : N) : t ≤ aIn t t' :=
  le_trans ((nf.le_iff _ _).mpr ⟨(t + t') * (t + t'), by unfold npair; ring⟩)
    (nf.le_add (npair t t') (npair t t'))

theorem le_aIn_right (t t' : N) : t' ≤ aIn t t' := by
  have h1 : t' ≤ t + t' := (nf.le_iff _ _).mpr ⟨t, add_comm t' t⟩
  have h2 : t + t' ≤ npair t t' := le_trans (nf.le_mul_self (t + t')) (nf.le_add _ t)
  exact le_trans (le_trans h1 h2) (nf.le_add (npair t t') (npair t t'))

theorem le_aEq_left (t t' : N) : t ≤ aEq t t' := le_trans (nf.le_aIn_left t t') (nf.le_add _ 1)

theorem le_aEq_right (t t' : N) : t' ≤ aEq t t' := le_trans (nf.le_aIn_right t t') (nf.le_add _ 1)

end NFacts

namespace Host

variable {H : Host}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- Two increasing sequences of the same length with the same values are equal. -/
theorem incSeq_app_eq (ar : H.Arith E num) {s s' : H.W} {n : N} (hs : H.IncSeq s (num n))
    (hs' : H.IncSeq s' (num n)) (hran : ∀ z, (∃ i, H.App s i z) ↔ ∃ i, H.App s' i z) :
    ∀ j : N, j + 1 ≤ n → ∀ b, H.App s (num j) b ↔ H.App s' (num j) b := by
  have aux : ∀ {s s' : H.W}, H.IncSeq s (num n) → H.IncSeq s' (num n) →
      (∀ z, (∃ i, H.App s i z) → ∃ i, H.App s' i z) → ∀ x0 a b, x0 ∈ num n →
      (∀ i, i ∈ x0 → ∀ u u', H.App s i u → H.App s' i u' → u = u') →
      H.App s x0 a → H.App s' x0 b → a ∈ b → False := by
    intro s s' hs hs' hran x0 a b hx0 hag ha hb hab
    obtain ⟨i, hi⟩ := hran a ⟨x0, ha⟩
    have hin := hs'.dom hi
    have hio := H.mem_om_of_mem hs.2.1 hin
    have hxo := H.mem_om_of_mem hs.2.1 hx0
    rcases H.om_tri i hio x0 hxo with h | h | h
    · obtain ⟨u, hu⟩ := hs.tot hin
      have e := hag i h u a hu hi
      rw [e] at hu
      exact H.mem_irrefl a (hs.2.2.2 i x0 a a hu ha h)
    · rw [h] at hi
      rw [hs'.fn hi hb] at hab
      exact H.mem_irrefl b hab
    · have hba := hs'.2.2.2 x0 i b a hb hi h
      exact H.lt_irrefl a (H.lt_trans _ _ _ (H.mem_lt _ _ hab) (H.mem_lt _ _ hba))
  have key : ¬ ∃ x, x ∈ num n ∧ ∃ a b, H.App s x a ∧ H.App s' x b ∧ a ≠ b := by
    rintro ⟨x, hx⟩
    obtain ⟨x0, ⟨hx0, a, b, ha, hb, hne⟩, hmin⟩ :=
      H.least' (fun x => x ∈ num n ∧ ∃ a b, H.App s x a ∧ H.App s' x b ∧ a ≠ b) (by hdef) hx
    have hag : ∀ i, i ∈ x0 → ∀ u u', H.App s i u → H.App s' i u' → u = u' := by
      intro i hi u u' hu hu'
      by_contra hne'
      exact hmin i (H.mem_lt _ _ hi) ⟨H.om_mem_trans hs.2.1 hx0 hi, u, u', hu, hu', hne'⟩
    rcases H.om_tri a (hs.2.2.1 _ _ ha) b (hs'.2.2.1 _ _ hb) with h | h | h
    · exact aux hs hs' (fun z => (hran z).mp) x0 a b hx0 hag ha hb h
    · exact hne h
    · exact aux hs' hs (fun z => (hran z).mpr) x0 b a hx0
        (fun i hi u u' hu hu' => (hag i hi u' u hu' hu).symm) hb ha h
  intro j hj b
  have hjn : num j ∈ num n := ar.num_mem.mpr hj
  obtain ⟨a, ha⟩ := hs.tot hjn
  obtain ⟨a', ha'⟩ := hs'.tot hjn
  have e : a = a' := by
    by_contra hne
    exact key ⟨num j, hjn, a, a', ha, ha', hne⟩
  subst e
  exact ⟨fun h => by rw [hs.fn h ha]; exact ha', fun h => by rw [hs'.fn h ha']; exact ha⟩

/-- The segment of an increasing sequence that starts at `m` and has the length `W`. -/
theorem exists_seg (ar : H.Arith E num) {w : H.W} {L : N} (hw : H.IncSeq w (num L)) (m W : N)
    (hmW : m + W ≤ L) :
    ∃ s, H.IncSeq s (num W) ∧ H.SubSeq s w ∧
      ∀ j : N, j + 1 ≤ W → ∀ b, H.App w (num (m + j)) b ↔ H.App s (num j) b := by
  have hA := ar.def_Ad
  have hfun : ∀ u ∈ num W, ∀ y y', (∃ z, ar.Ad (num m) u z ∧ H.App w z y) →
      (∃ z, ar.Ad (num m) u z ∧ H.App w z y') → y = y' := by
    rintro u hu y y' ⟨z, hz, hy⟩ ⟨z', hz', hy'⟩
    obtain ⟨j, -, rfl⟩ := ar.mem_num.mp hu
    rw [ar.ad_iff.mp hz] at hy
    rw [ar.ad_iff.mp hz'] at hy'
    exact hw.fn hy hy'
  let s := H.mkFun (num W) (fun x y => ∃ z, ar.Ad (num m) x z ∧ H.App w z y) (by hdef) hfun
  have happ : ∀ (j : N) (b : H.W), H.App s (num j) b ↔ j + 1 ≤ W ∧ H.App w (num (m + j)) b := by
    intro j b
    rw [show H.App s (num j) b ↔ num j ∈ num W ∧ ∃ z, ar.Ad (num m) (num j) z ∧ H.App w z b
      from H.app_mkFun, ar.num_mem]
    constructor
    · rintro ⟨h1, z, hz, hb⟩
      rw [ar.ad_iff.mp hz] at hb
      exact ⟨h1, hb⟩
    · rintro ⟨h1, hb⟩
      exact ⟨h1, _, ar.ad_iff.mpr rfl, hb⟩
  have hin : ∀ j : N, j + 1 ≤ W → num (m + j) ∈ num L := fun j hj =>
    ar.num_mem.mpr (le_trans (by rw [add_assoc]; exact ar.nf.add_le_add_l hj m) hmW)
  refine ⟨s, ⟨⟨H.isFun_mkFun, fun a => ⟨fun ha => ?_, fun ⟨b, hb⟩ => (H.app_mkFun.mp hb).1⟩⟩,
    ar.num_om W, ?_, ?_⟩, ?_, fun j hj b => ⟨fun h => (happ j b).mpr ⟨hj, h⟩,
      fun h => ((happ j b).mp h).2⟩⟩
  · obtain ⟨j, hj, rfl⟩ := ar.mem_num.mp ha
    obtain ⟨b, hb⟩ := hw.tot (hin j hj)
    exact ⟨b, (happ j b).mpr ⟨hj, hb⟩⟩
  · intro i a hi
    obtain ⟨hi1, z, -, hz⟩ := H.app_mkFun.mp hi
    exact hw.2.2.1 _ _ hz
  · intro i i' a b hi hi' hii
    have hi1 := (H.app_mkFun.mp hi).1
    have hi1' := (H.app_mkFun.mp hi').1
    obtain ⟨j, hj, rfl⟩ := ar.mem_num.mp hi1
    obtain ⟨j', hj', rfl⟩ := ar.mem_num.mp hi1'
    refine hw.2.2.2 _ _ a b ((happ j a).mp hi).2 ((happ j' b).mp hi').2 (ar.num_mem.mpr ?_)
    rw [add_assoc]
    exact ar.nf.add_le_add_l (ar.num_mem.mp hii) m
  · intro i a hi
    obtain ⟨-, z, -, hz⟩ := H.app_mkFun.mp hi
    exact ⟨z, hz⟩

/-- A set that contains every set of `r` members of `X`. -/
theorem exists_finSubsets (ar : H.Arith E num) (X : H.W) :
    ∀ r : N, ∃ A : H.W, ∀ B : H.W, H.Card B (num r) → H.Sub B X → B ∈ A := by
  have hdc := H.def_card
  refine ar.num_ind (fun x => ∃ A : H.W, ∀ B : H.W, H.Card B x → H.Sub B X → B ∈ A) (by hdef) ?_ ?_
  · refine ⟨H.sg H.emp, fun B hB _ => H.mem_sg.mpr ?_⟩
    obtain ⟨s, hs, hsm⟩ := hB
    refine H.eq_emp fun z hz => ?_
    obtain ⟨i, hi⟩ := (hsm z).mp hz
    have := hs.dom hi
    rw [ar.iso.zero] at this
    exact H.not_mem_emp i this
  · rintro r ⟨A, hA⟩
    obtain ⟨A', hA'⟩ := H.repl' (H.prod A X)
      (fun p y => ∃ B0 z, p = H.op B0 z ∧ y = H.bun B0 (H.sg z)) (by hdef)
      (by
        rintro u - y y' ⟨B0, z, e, rfl⟩ ⟨B0', z', e', rfl⟩
        obtain ⟨e1, e2⟩ := H.op_inj (e.symm.trans e')
        rw [e1, e2])
    refine ⟨A', fun B hB hBX => ?_⟩
    obtain ⟨s, hs, hsm⟩ := hB
    have hrd : num r ∈ num (r + 1) := ar.num_mem.mpr (le_refl _)
    obtain ⟨x, hx⟩ := hs.tot hrd
    have hs0 := hs.res (ar.num_om r) (ar.num_sub (ar.nf.le_add r 1))
    have hxB : x ∈ B := (hsm x).mpr ⟨_, hx⟩
    have hB0 : H.Card (H.ran (H.res s (num r))) (num r) := ⟨_, hs0, fun z => H.mem_ran⟩
    have hsub : H.Sub (H.ran (H.res s (num r))) X := fun z hz => by
      obtain ⟨i, hi⟩ := H.mem_ran.mp hz
      exact hBX z ((hsm z).mpr ⟨i, (H.app_res.mp hi).2⟩)
    refine (hA' B).mpr ⟨H.op (H.ran (H.res s (num r))) x,
      H.op_mem_prod.mpr ⟨hA _ hB0 hsub, hBX x hxB⟩, _, _, rfl, H.ext' fun z => ?_⟩
    rw [H.mem_bun, H.mem_sg, H.mem_ran, hsm z]
    constructor
    · rintro ⟨i, hi⟩
      have hid := hs.dom hi
      rw [ar.iso.succ] at hid
      rcases H.mem_suc.mp hid with h | h
      · exact Or.inl ⟨i, H.app_res.mpr ⟨h, hi⟩⟩
      · rw [h] at hi
        exact Or.inr (hs.fn hi hx)
    · rintro (⟨i, hi⟩ | h)
      · exact ⟨i, (H.app_res.mp hi).2⟩
      · rw [h]
        exact ⟨_, hx⟩

end Host

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- The atom `n ∈ n'` at the position `k` of the placement `v`, as a relation. -/
def TinR (Fm : FlatM H) (ar : H.Arith E num) (n n' k v : H.W) : Prop :=
  ∃ c c' a a', Fm.Val ar n k v c ∧ Fm.Val ar n' (H.suc k) v c' ∧ H.App v k a ∧
    H.App v (H.suc k) a' ∧ Fm.El c c' (H.op a' a)

/-- The atom `n = n'` at the position `k` of the placement `v`, as a relation. -/
def TeqR (Fm : FlatM H) (ar : H.Arith E num) (n n' k v : H.W) : Prop :=
  ∃ c, Fm.Val ar n k v c ∧ Fm.Val ar n' k v c

theorem tinR_iff (ar : H.Arith E num) (ax : Fm.Ax) {v k : H.W} (hv : Fm.Plc v)
    (hp1 : ∃ b, H.App v (H.suc k) b) (t t' : N) :
    Fm.TinR ar (num t) (num t') k v ↔ Fm.Tin ar t t' k v := by
  have hp0 := hv.down hp1
  constructor
  · rintro ⟨c, c', a, a', h1, h2, h3, h4, h5⟩
    rw [val_eq ar ax hv h1, val_eq ar ax hv h2, H.lvl_eq hv.fn h3, H.lvl_eq hv.fn h4] at h5
    exact h5
  · intro h
    exact ⟨_, _, _, _, vl_spec ar ax hv hp0, vl_spec ar ax hv hp1, H.lvl_spec hp0,
      H.lvl_spec hp1, h⟩

theorem teqR_iff (ar : H.Arith E num) (ax : Fm.Ax) {v k : H.W} (hv : Fm.Plc v)
    (hp0 : ∃ b, H.App v k b) (t t' : N) :
    Fm.TeqR ar (num t) (num t') k v ↔ Fm.Teq ar t t' k v := by
  constructor
  · rintro ⟨c, h1, h2⟩
    unfold Teq
    rw [← val_eq ar ax hv h1, ← val_eq ar ax hv h2]
  · intro h
    refine ⟨_, vl_spec ar ax hv hp0, ?_⟩
    unfold Teq at h
    rw [h]
    exact vl_spec ar ax hv hp0

/-- `i` is the code of the atom `n ∈ n'`. -/
def AtIn (ar : H.Arith E num) (i n n' : H.W) : Prop := ∃ p, ar.Pr n n' p ∧ ar.Ad p p i

/-- `i` is the code of the atom `n = n'`. -/
def AtEq (ar : H.Arith E num) (i n n' : H.W) : Prop :=
  ∃ p s, ar.Pr n n' p ∧ ar.Ad p p s ∧ i = H.suc s

/-- The atom with the code `i` is true at the position `k` of the placement `v`. -/
def Tr (Fm : FlatM H) (ar : H.Arith E num) (i k v : H.W) : Prop :=
  (∃ n n', n ∈ H.om ∧ n' ∈ H.om ∧ AtIn ar i n n' ∧ Fm.TinR ar n n' k v) ∨
    (∃ n n', n ∈ H.om ∧ n' ∈ H.om ∧ AtEq ar i n n' ∧ Fm.TeqR ar n n' k v)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem def_tr (ar : H.Arith E num) : Def3 H (Fm.Tr ar) := by
  have h1 := Fm.def_vl ar
  have h2 := Fm.defEl
  have h3 := ar.def_Ad
  have h4 := ar.def_Mu
  hdef

theorem tr_cases (ar : H.Arith E num) {i : N} {k v : H.W} : Fm.Tr ar (num i) k v ↔
    (∃ t t' : N, i = aIn t t' ∧ Fm.TinR ar (num t) (num t') k v) ∨
      (∃ t t' : N, i = aEq t t' ∧ Fm.TeqR ar (num t) (num t') k v) := by
  constructor
  · rintro (⟨n, n', hn, hn', ⟨p, hp, hi⟩, h⟩ | ⟨n, n', hn, hn', ⟨p, s, hp, hs, hi⟩, h⟩)
    · obtain ⟨t, rfl⟩ := ar.of_om hn
      obtain ⟨t', rfl⟩ := ar.of_om hn'
      rw [ar.pr_iff.mp hp] at hi
      exact Or.inl ⟨t, t', ar.num_inj (ar.ad_iff.mp hi), h⟩
    · obtain ⟨t, rfl⟩ := ar.of_om hn
      obtain ⟨t', rfl⟩ := ar.of_om hn'
      rw [ar.pr_iff.mp hp] at hs
      rw [ar.ad_iff.mp hs, ← ar.iso.succ] at hi
      exact Or.inr ⟨t, t', ar.num_inj hi, h⟩
  · rintro (⟨t, t', rfl, h⟩ | ⟨t, t', rfl, h⟩)
    · exact Or.inl ⟨_, _, ar.num_om t, ar.num_om t', ⟨_, ar.pr_iff.mpr rfl, ar.ad_iff.mpr rfl⟩, h⟩
    · exact Or.inr ⟨_, _, ar.num_om t, ar.num_om t',
        ⟨_, _, ar.pr_iff.mpr rfl, ar.ad_iff.mpr rfl, ar.iso.succ _⟩, h⟩

theorem tr_in (ar : H.Arith E num) {t t' : N} {k v : H.W} :
    Fm.Tr ar (num (aIn t t')) k v ↔ Fm.TinR ar (num t) (num t') k v := by
  rw [tr_cases ar]
  constructor
  · rintro (⟨x, y, e, h⟩ | ⟨x, y, e, h⟩)
    · obtain ⟨e1, e2⟩ := ar.nf.pair_inj _ _ _ _ (ar.nf.double_inj e)
      rw [e1, e2]
      exact h
    · exact (ar.nf.double_ne e).elim
  · exact fun h => Or.inl ⟨t, t', rfl, h⟩

theorem tr_eq (ar : H.Arith E num) {t t' : N} {k v : H.W} :
    Fm.Tr ar (num (aEq t t')) k v ↔ Fm.TeqR ar (num t) (num t') k v := by
  rw [tr_cases ar]
  constructor
  · rintro (⟨x, y, e, h⟩ | ⟨x, y, e, h⟩)
    · exact (ar.nf.double_ne e.symm).elim
    · obtain ⟨e1, e2⟩ := ar.nf.pair_inj _ _ _ _ (ar.nf.double_inj (ar.nf.succ_inj e))
      rw [e1, e2]
      exact h
  · exact fun h => Or.inr ⟨t, t', rfl, h⟩

/-- Locality for atoms: the radius of the atom `i` is `5 i + 6`. -/
theorem tr_loc (ar : H.Arith E num) {v w : H.W} {m W : N}
    (hseg : ∀ j : N, j + 1 ≤ W → ∀ b, H.App v (num (m + j)) b ↔ H.App w (num j) b) (i : N)
    {k k' : H.W} (hI : Iseg num m W (5 * i + 6) k k') :
    Fm.Tr ar (num i) k v ↔ Fm.Tr ar (num i) k' w := by
  have hbis := bis_seg ar hseg
  have h0 : Iseg num m W 0 k k' := hbis.mono 0 (5 * i + 6) k k' (by rw [zero_add]; exact hI)
  have h0' : Iseg num m W 0 (H.suc k) (H.suc k') := hbis.up 0 _ _ (hbis.mono (0 + 1) (5 * i + 5)
    k k' (by rw [show (0 : N) + 1 + (5 * i + 5) = 5 * i + 6 from by ring]; exact hI))
  have hle : ∀ t : N, t ≤ i → Iseg num m W (5 * t + 5) k k' ∧
      Iseg num m W (5 * t + 5) (H.suc k) (H.suc k') := by
    intro t ht
    obtain ⟨s, rfl⟩ := (ar.nf.le_iff _ _).mp ht
    exact ⟨hbis.mono _ (5 * s + 1) k k' (by
        rw [show 5 * t + 5 + (5 * s + 1) = 5 * (t + s) + 6 from by ring]; exact hI),
      hbis.up _ _ _ (hbis.mono _ (5 * s) k k' (by
        rw [show 5 * t + 5 + 1 + 5 * s = 5 * (t + s) + 6 from by ring]; exact hI))⟩
  rw [tr_cases ar, tr_cases ar]
  refine or_congr (exists_congr fun t => exists_congr fun t' => and_congr_right fun e => ?_)
    (exists_congr fun t => exists_congr fun t' => and_congr_right fun e => ?_)
  · have ht := hle t (by rw [e]; exact ar.nf.le_aIn_left t t')
    have ht' := hle t' (by rw [e]; exact ar.nf.le_aIn_right t t')
    exact exists_congr fun c => exists_congr fun c' => exists_congr fun a => exists_congr fun a' =>
      and_congr (loc ar hseg t k k' c ht.1) (and_congr (loc ar hseg t' _ _ c' ht'.2)
        (and_congr (hbis.app 0 _ _ h0 a) (and_congr (hbis.app 0 _ _ h0' a') Iff.rfl)))
  · have ht := hle t (by rw [e]; exact ar.nf.le_aEq_left t t')
    have ht' := hle t' (by rw [e]; exact ar.nf.le_aEq_right t t')
    exact exists_congr fun c => and_congr (loc ar hseg t k k' c ht.1) (loc ar hseg t' k k' c ht'.1)

/-- The atom `i` is true at every position of every sequence drawn from `e`, at distance at
least `R` from the ends. -/
def AllT (Fm : FlatM H) (ar : H.Arith E num) (e i R : H.W) : Prop :=
  ∀ w L p, H.IncSeq w L → H.SubSeq w e → p ∈ L → (R ∈ p ∨ R = p) →
    (∃ s, ar.Ad p R s ∧ s ∈ L) → Fm.Tr ar i p w

/-- The atom `i` is false at every such position. -/
def AllF (Fm : FlatM H) (ar : H.Arith E num) (e i R : H.W) : Prop :=
  ∀ w L p, H.IncSeq w L → H.SubSeq w e → p ∈ L → (R ∈ p ∨ R = p) →
    (∃ s, ar.Ad p R s ∧ s ∈ L) → ¬ Fm.Tr ar i p w

theorem allT_iff (ar : H.Arith E num) {e i : H.W} {R : N} : Fm.AllT ar e i (num R) ↔
    ∀ (w : H.W) (L p : N), H.IncSeq w (num L) → H.SubSeq w e → R ≤ p → p + R + 1 ≤ L →
      Fm.Tr ar i (num p) w := by
  constructor
  · intro h w L p hw hwe h1 h2
    exact h w (num L) (num p) hw hwe
      (ar.num_mem.mpr (le_trans (ar.nf.add_le_add_r (ar.nf.le_add p R) 1) h2))
      (ar.num_le.mpr h1) ⟨_, ar.ad_iff.mpr rfl, ar.num_mem.mpr h2⟩
  · intro h w L p hw hwe hp h1 ⟨s, hs, hsL⟩
    obtain ⟨L', rfl⟩ := ar.of_om hw.2.1
    obtain ⟨p', -, rfl⟩ := ar.mem_num.mp hp
    rw [ar.ad_iff.mp hs] at hsL
    exact h w L' p' hw hwe (ar.num_le.mp h1) (ar.num_mem.mp hsL)

theorem allF_iff (ar : H.Arith E num) {e i : H.W} {R : N} : Fm.AllF ar e i (num R) ↔
    ∀ (w : H.W) (L p : N), H.IncSeq w (num L) → H.SubSeq w e → R ≤ p → p + R + 1 ≤ L →
      ¬ Fm.Tr ar i (num p) w := by
  constructor
  · intro h w L p hw hwe h1 h2
    exact h w (num L) (num p) hw hwe
      (ar.num_mem.mpr (le_trans (ar.nf.add_le_add_r (ar.nf.le_add p R) 1) h2))
      (ar.num_le.mpr h1) ⟨_, ar.ad_iff.mpr rfl, ar.num_mem.mpr h2⟩
  · intro h w L p hw hwe hp h1 ⟨s, hs, hsL⟩
    obtain ⟨L', rfl⟩ := ar.of_om hw.2.1
    obtain ⟨p', -, rfl⟩ := ar.mem_num.mp hp
    rw [ar.ad_iff.mp hs] at hsL
    exact h w L' p' hw hwe (ar.num_le.mp h1) (ar.num_mem.mp hsL)

theorem AllT.sub {ar : H.Arith E num} {e e' i R : H.W} (h : Fm.AllT ar e' i R)
    (hs : H.SubSeq e e') : Fm.AllT ar e i R :=
  fun w L p hw hwe => h w L p hw (hwe.trans hs)

theorem AllF.sub {ar : H.Arith E num} {e e' i R : H.W} (h : Fm.AllF ar e' i R)
    (hs : H.SubSeq e e') : Fm.AllF ar e i R :=
  fun w L p hw hwe => h w L p hw (hwe.trans hs)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **Deciding one more atom.** If the Ramsey property holds for the exponent `2R + 1`, every
increasing sequence of length `Q` has a subsequence of length `q` on which the atom `i`, of
radius at most `R`, is decided. -/
theorem decide_atom (ar : H.Arith E num) {e' q Q : H.W} {i R : N} (hrad : 5 * i + 6 ≤ R)
    (he' : H.IncSeq e' Q) (hram : H.Ram (num (R + R + 1)) q Q) :
    ∃ e, H.IncSeq e q ∧ H.SubSeq e e' ∧
      (Fm.AllT ar e (num i) (num R) ∨ Fm.AllF ar e (num i) (num R)) := by
  have hdt := Fm.def_tr ar
  have hdi := H.def_incSeq
  obtain ⟨A, hA⟩ := H.exists_finSubsets ar (H.ran e') (R + R + 1)
  obtain ⟨c, hc⟩ := H.sep' A (fun B => ∃ s, H.IncSeq s (num (R + R + 1)) ∧
    (∀ z, z ∈ B ↔ ∃ j, H.App s j z) ∧ Fm.Tr ar (num i) (num R) s) (by hdef)
  obtain ⟨g, hg, hge, hhom⟩ := hram c e' he'
  -- the segment of a sequence around a position, and its colour
  have seg : ∀ (w : H.W) (L p : N), H.IncSeq w (num L) → H.SubSeq w g → R ≤ p → p + R + 1 ≤ L →
      ∃ s, H.IncSeq s (num (R + R + 1)) ∧ H.SubSeq s g ∧
        (Fm.Tr ar (num i) (num p) w ↔ Fm.Tr ar (num i) (num R) s) := by
    intro w L p hw hwg h1 h2
    obtain ⟨m, rfl⟩ := (ar.nf.le_iff _ _).mp h1
    obtain ⟨s, hs, hsw, hseg⟩ := H.exists_seg ar hw m (R + R + 1) (by
      rw [show m + (R + R + 1) = R + m + R + 1 from by ring]; exact h2)
    refine ⟨s, hs, hsw.trans hwg, ?_⟩
    rw [show R + m = m + R from add_comm R m]
    exact tr_loc ar hseg i
      ⟨R, hrad, ar.nf.add_le_add_r (ar.nf.add_le_add_l hrad R) 1, rfl, rfl⟩
  -- the colour of the set of the values of a sequence of length `2R + 1`
  have hcol : ∀ s, H.IncSeq s (num (R + R + 1)) → H.SubSeq s g →
      (H.ran s ∈ c ↔ Fm.Tr ar (num i) (num R) s) ∧ H.Card (H.ran s) (num (R + R + 1)) ∧
        H.SubV (H.ran s) g := by
    intro s hs hsg
    have hcard : H.Card (H.ran s) (num (R + R + 1)) := ⟨s, hs, fun z => H.mem_ran⟩
    have hsub : H.Sub (H.ran s) (H.ran e') := fun z hz => by
      obtain ⟨j, hj⟩ := H.mem_ran.mp hz
      obtain ⟨j', hj'⟩ := hsg j z hj
      obtain ⟨j'', hj''⟩ := hge j' z hj'
      exact H.mem_ran.mpr ⟨j'', hj''⟩
    refine ⟨?_, hcard, fun b hb => ?_⟩
    · rw [hc]
      constructor
      · rintro ⟨-, s', hs', hran, htr⟩
        have hsame := H.incSeq_app_eq ar hs' hs (fun z => (hran z).symm.trans H.mem_ran)
        have hseg0 : ∀ j : N, j + 1 ≤ R + R + 1 → ∀ b,
            H.App s' (num (0 + j)) b ↔ H.App s (num j) b := fun j hj b => by
          rw [zero_add]
          exact hsame j hj b
        exact (tr_loc ar hseg0 i ⟨R, hrad, ar.nf.add_le_add_r (ar.nf.add_le_add_l hrad R) 1,
          by rw [zero_add], rfl⟩).mp htr
      · intro htr
        exact ⟨hA _ hcard hsub, s, hs, fun z => H.mem_ran, htr⟩
    · obtain ⟨j, hj⟩ := H.mem_ran.mp hb
      exact hsg j b hj
  refine ⟨g, hg, hge, ?_⟩
  by_cases hex : ∃ s, H.IncSeq s (num (R + R + 1)) ∧ H.SubSeq s g ∧ Fm.Tr ar (num i) (num R) s
  · obtain ⟨s0, hs0, hs0g, htr0⟩ := hex
    obtain ⟨hc0, hcard0, hsub0⟩ := hcol s0 hs0 hs0g
    refine Or.inl ((allT_iff ar).mpr fun w L p hw hwg h1 h2 => ?_)
    obtain ⟨s, hs, hsg, hiff⟩ := seg w L p hw hwg h1 h2
    obtain ⟨hcs, hcards, hsubs⟩ := hcol s hs hsg
    exact hiff.mpr (hcs.mp ((hhom _ _ hcard0 hcards hsub0 hsubs).mp (hc0.mpr htr0)))
  · refine Or.inr ((allF_iff ar).mpr fun w L p hw hwg h1 h2 htr => ?_)
    obtain ⟨s, hs, hsg, hiff⟩ := seg w L p hw hwg h1 h2
    exact hex ⟨s, hs, hsg, hiff.mp htr⟩

end FlatM

/-! ## Phase 2 (A8): the truth assignment read off a sequence of levels satisfies the axioms N

`NSat τ q`: the truth assignment `τ` on the codes of atoms satisfies every instance of the
axioms N all of whose atoms have codes below `q`. Generated by `gen/gen53.py`. -/

/-- The truth assignment `τ` satisfies every instance of the axioms N whose atoms have codes
below `q`. -/
structure NSat {N : Type} [CommSemiring N] [PartialOrder N] (τ : N → Prop) (q : N) : Prop where
  e1 : ∀ x : N, aEq (x) (x) + 1 ≤ q →
    τ (aEq (x) (x))
  e2 : ∀ x y z : N, aEq (x) (y) + 1 ≤ q → aEq (x) (z) + 1 ≤ q → aEq (y) (z) + 1 ≤ q →
    τ (aEq (x) (y)) → τ (aEq (x) (z)) → τ (aEq (y) (z))
  e3 : ∀ x x' y y' : N, aEq (x) (x') + 1 ≤ q → aEq (y) (y') + 1 ≤ q → aIn (x) (y) + 1 ≤ q → aIn (x') (y') + 1 ≤ q →
    τ (aEq (x) (x')) → τ (aEq (y) (y')) → τ (aIn (x) (y)) → τ (aIn (x') (y'))
  e4a : ∀ x x' : N, aEq (x) (x') + 1 ≤ q → aEq (sgT x) (sgT x') + 1 ≤ q →
    τ (aEq (x) (x')) → τ (aEq (sgT x) (sgT x'))
  e4b : ∀ x x' y y' : N, aEq (x) (x') + 1 ≤ q → aEq (y) (y') + 1 ≤ q → aEq (upT x y) (upT x' y') + 1 ≤ q →
    τ (aEq (x) (x')) → τ (aEq (y) (y')) → τ (aEq (upT x y) (upT x' y'))
  m1 : ∀ x y : N, aIn (dT x y) (x) + 1 ≤ q → aIn (dT x y) (y) + 1 ≤ q → aEq (x) (y) + 1 ≤ q →
    (τ (aIn (dT x y) (x)) ↔ τ (aIn (dT x y) (y))) → τ (aEq (x) (y))
  m2 : ∀ x y : N, aIn (y) (sgT x) + 1 ≤ q → aEq (y) (x) + 1 ≤ q →
    (τ (aIn (y) (sgT x)) ↔ τ (aEq (y) (x)))
  m3 : ∀ x y z : N, aIn (z) (upT x y) + 1 ≤ q → aEq (z) (x) + 1 ≤ q → aEq (z) (y) + 1 ≤ q →
    (τ (aIn (z) (upT x y)) ↔ τ (aEq (z) (x)) ∨ τ (aEq (z) (y)))
  m4 : ∀ x y z : N, aIn (z) (inT x y) + 1 ≤ q → aIn (z) (x) + 1 ≤ q → aIn (z) (y) + 1 ≤ q →
    (τ (aIn (z) (inT x y)) ↔ τ (aIn (z) (x)) ∧ τ (aIn (z) (y)))
  m5 : ∀ x z : N, aIn (z) (coT x) + 1 ≤ q → aIn (z) (x) + 1 ≤ q →
    (τ (aIn (z) (coT x)) ↔ ¬ τ (aIn (z) (x)))
  m6 : ∀ x z w : N, aIn (opT (sgT z) (sgT w)) (siT x) + 1 ≤ q → aIn (opT z w) (x) + 1 ≤ q →
    (τ (aIn (opT (sgT z) (sgT w)) (siT x)) ↔ τ (aIn (opT z w) (x)))
  m7 : ∀ x p s r : N, aIn (opT (sgT (sgT p)) (opT s r)) (i2T x) + 1 ≤ q → aIn (opT p r) (x) + 1 ≤ q →
    (τ (aIn (opT (sgT (sgT p)) (opT s r)) (i2T x)) ↔ τ (aIn (opT p r) (x)))
  m8 : ∀ x p s r : N, aIn (opT (sgT (sgT p)) (opT s r)) (i3T x) + 1 ≤ q → aIn (opT p s) (x) + 1 ≤ q →
    (τ (aIn (opT (sgT (sgT p)) (opT s r)) (i3T x)) ↔ τ (aIn (opT p s) (x)))
  m9a : ∀ x p : N, aIn (p) (vcT x) + 1 ≤ q → aEq (p) (opT (p1T p) (p2T p)) + 1 ≤ q → aIn (p2T p) (x) + 1 ≤ q →
    τ (aIn (p) (vcT x)) → τ (aEq (p) (opT (p1T p) (p2T p))) ∧ τ (aIn (p2T p) (x))
  m9b : ∀ x p s r : N, aEq (p) (opT s r) + 1 ≤ q → aIn (r) (x) + 1 ≤ q → aIn (p) (vcT x) + 1 ≤ q →
    τ (aEq (p) (opT s r)) → τ (aIn (r) (x)) → τ (aIn (p) (vcT x))
  m10a : ∀ x p s : N, aIn (p) (tlT x) + 1 ≤ q → aIn (opT s (sgT p)) (x) + 1 ≤ q →
    τ (aIn (p) (tlT x)) → τ (aIn (opT s (sgT p)) (x))
  m10b : ∀ x p : N, aIn (opT (wtT p x) (sgT p)) (x) + 1 ≤ q → aIn (p) (tlT x) + 1 ≤ q →
    τ (aIn (opT (wtT p x) (sgT p)) (x)) → τ (aIn (p) (tlT x))
  m11 : ∀ x p s : N, aIn (opT p s) (cvT x) + 1 ≤ q → aIn (opT s p) (x) + 1 ≤ q →
    (τ (aIn (opT p s) (cvT x)) ↔ τ (aIn (opT s p) (x)))
  m12a : ∀ p : N, aIn (p) (c1T) + 1 ≤ q → aEq (p) (sgT (elT p)) + 1 ≤ q →
    τ (aIn (p) (c1T)) → τ (aEq (p) (sgT (elT p)))
  m12b : ∀ p s : N, aEq (p) (sgT s) + 1 ≤ q → aIn (p) (c1T) + 1 ≤ q →
    τ (aEq (p) (sgT s)) → τ (aIn (p) (c1T))
  m13a : ∀ p s r : N, aIn (opT p s) (sbT) + 1 ≤ q → aIn (r) (p) + 1 ≤ q → aIn (r) (s) + 1 ≤ q →
    τ (aIn (opT p s) (sbT)) → τ (aIn (r) (p)) → τ (aIn (r) (s))
  m13b : ∀ p s : N, aIn (wsT p s) (p) + 1 ≤ q → aIn (wsT p s) (s) + 1 ≤ q → aIn (opT p s) (sbT) + 1 ≤ q →
    (τ (aIn (wsT p s) (p)) → τ (aIn (wsT p s) (s))) → τ (aIn (opT p s) (sbT))

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- **The truth assignment of a sequence of levels on which the atoms below `q` are decided
satisfies the axioms N below `q`.** -/
theorem nsat_of_dec (ar : H.Arith E num) (ax : Fm.Ax) {e : H.W} {q R l : N}
    (he : H.IncSeq e (num l)) (hlv : ∀ k a, H.App e k a → Fm.Lv a) (hl : R + 5 + R + 1 ≤ l)
    (hdec : ∀ i : N, i + 1 ≤ q → Fm.AllT ar e (num i) (num R) ∨ Fm.AllF ar e (num i) (num R)) :
    NSat (fun i => Fm.AllT ar e (num i) (num R)) q := by
  have hv : Fm.Plc e := ⟨⟨_, he⟩, hlv⟩
  have tv : ∀ i P : N, i + 1 ≤ q → R ≤ P → P + R + 1 ≤ l →
      (Fm.AllT ar e (num i) (num R) ↔ Fm.Tr ar (num i) (num P) e) := by
    intro i P hi h1 h2
    constructor
    · exact fun h => (allT_iff ar).mp h e l P he (fun j a hj => ⟨j, hj⟩) h1 h2
    · intro htr
      rcases hdec i hi with h | h
      · exact h
      · exact ((allF_iff ar).mp h e l P he (fun j a hj => ⟨j, hj⟩) h1 h2 htr).elim
  have hp5 : ∃ b, H.App e (H.suc (H.suc (H.suc (H.suc (H.suc (num R)))))) b := by
    rw [← ar.iso.succ, ← ar.iso.succ, ← ar.iso.succ, ← ar.iso.succ, ← ar.iso.succ]
    exact he.tot (ar.num_mem.mpr (le_trans ((ar.nf.le_iff _ _).mpr ⟨R, by ring⟩) hl))
  have hp4 := hv.down hp5
  have hp3 := hv.down hp4
  have hp2 := hv.down hp3
  have hp1 := hv.down hp2
  have hp0 := hv.down hp1
  have kI0 : ∀ t t' : N, aIn t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aIn t t')) (num R) ↔ Fm.Tin ar t t' (num R) e) := by
    intro t t' hi
    have h := tv (aIn t t') (R) hi ((ar.nf.le_iff _ _).mpr ⟨0, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨5, by ring⟩) hl)
    exact h.trans ((tr_in ar).trans (tinR_iff ar ax hv hp1 t t'))
  have kI1 : ∀ t t' : N, aIn t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aIn t t')) (num R) ↔ Fm.Tin ar t t' (H.suc (num R)) e) := by
    intro t t' hi
    have h := tv (aIn t t') (R + 1) hi ((ar.nf.le_iff _ _).mpr ⟨1, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨4, by ring⟩) hl)
    rw [ar.iso.succ] at h
    exact h.trans ((tr_in ar).trans (tinR_iff ar ax hv hp2 t t'))
  have kI2 : ∀ t t' : N, aIn t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aIn t t')) (num R) ↔ Fm.Tin ar t t' (H.suc (H.suc (num R))) e) := by
    intro t t' hi
    have h := tv (aIn t t') (R + 1 + 1) hi ((ar.nf.le_iff _ _).mpr ⟨2, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨3, by ring⟩) hl)
    rw [ar.iso.succ, ar.iso.succ] at h
    exact h.trans ((tr_in ar).trans (tinR_iff ar ax hv hp3 t t'))
  have kI3 : ∀ t t' : N, aIn t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aIn t t')) (num R) ↔ Fm.Tin ar t t' (H.suc (H.suc (H.suc (num R)))) e) := by
    intro t t' hi
    have h := tv (aIn t t') (R + 1 + 1 + 1) hi ((ar.nf.le_iff _ _).mpr ⟨3, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨2, by ring⟩) hl)
    rw [ar.iso.succ, ar.iso.succ, ar.iso.succ] at h
    exact h.trans ((tr_in ar).trans (tinR_iff ar ax hv hp4 t t'))
  have kI4 : ∀ t t' : N, aIn t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aIn t t')) (num R) ↔ Fm.Tin ar t t' (H.suc (H.suc (H.suc (H.suc (num R))))) e) := by
    intro t t' hi
    have h := tv (aIn t t') (R + 1 + 1 + 1 + 1) hi ((ar.nf.le_iff _ _).mpr ⟨4, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨1, by ring⟩) hl)
    rw [ar.iso.succ, ar.iso.succ, ar.iso.succ, ar.iso.succ] at h
    exact h.trans ((tr_in ar).trans (tinR_iff ar ax hv hp5 t t'))
  have kE0 : ∀ t t' : N, aEq t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aEq t t')) (num R) ↔ Fm.Teq ar t t' (num R) e) := by
    intro t t' hi
    have h := tv (aEq t t') (R) hi ((ar.nf.le_iff _ _).mpr ⟨0, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨5, by ring⟩) hl)
    exact h.trans ((tr_eq ar).trans (teqR_iff ar ax hv hp0 t t'))
  have kE1 : ∀ t t' : N, aEq t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aEq t t')) (num R) ↔ Fm.Teq ar t t' (H.suc (num R)) e) := by
    intro t t' hi
    have h := tv (aEq t t') (R + 1) hi ((ar.nf.le_iff _ _).mpr ⟨1, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨4, by ring⟩) hl)
    rw [ar.iso.succ] at h
    exact h.trans ((tr_eq ar).trans (teqR_iff ar ax hv hp1 t t'))
  have kE2 : ∀ t t' : N, aEq t t' + 1 ≤ q →
      (Fm.AllT ar e (num (aEq t t')) (num R) ↔ Fm.Teq ar t t' (H.suc (H.suc (num R))) e) := by
    intro t t' hi
    have h := tv (aEq t t') (R + 1 + 1) hi ((ar.nf.le_iff _ _).mpr ⟨2, by ring⟩)
      (le_trans ((ar.nf.le_iff _ _).mpr ⟨3, by ring⟩) hl)
    rw [ar.iso.succ, ar.iso.succ] at h
    exact h.trans ((tr_eq ar).trans (teqR_iff ar ax hv hp2 t t'))
  exact
    { e1 := fun x h => (kE0 _ _ h).mpr (n_e1 ar x _ _)
      e2 := fun x y z h1 h2 h3 a b =>
        (kE0 _ _ h3).mpr (n_e2 ar ((kE0 _ _ h1).mp a) ((kE0 _ _ h2).mp b))
      e3 := fun x x' y y' h1 h2 h3 h4 a b c =>
        (kI0 _ _ h4).mpr (n_e3 ar ((kE0 _ _ h1).mp a) ((kE1 _ _ h2).mp b) ((kI0 _ _ h3).mp c))
      e4a := fun x x' h1 h2 a => (kE1 _ _ h2).mpr (n_e4a ar ax hv x x' hp1 ((kE0 _ _ h1).mp a))
      e4b := fun x x' y y' h1 h2 h3 a b =>
        (kE1 _ _ h3).mpr (n_e4b ar ax hv x x' y y' hp1 ((kE0 _ _ h1).mp a) ((kE0 _ _ h2).mp b))
      m1 := fun x y h1 h2 h3 hiff =>
        (kE1 _ _ h3).mpr (n_m1 ar ax hv x y hp1 (((kI0 _ _ h1).symm.trans hiff).trans (kI0 _ _ h2)))
      m2 := fun x y h1 h2 => (kI0 _ _ h1).trans ((n_m2 ar ax hv x y hp1).trans (kE0 _ _ h2).symm)
      m3 := fun x y z h1 h2 h3 => (kI0 _ _ h1).trans
        ((n_m3 ar ax hv x y z hp1).trans (or_congr (kE0 _ _ h2).symm (kE0 _ _ h3).symm))
      m4 := fun x y z h1 h2 h3 => (kI0 _ _ h1).trans
        ((n_m4 ar ax hv x y z hp1).trans (and_congr (kI0 _ _ h2).symm (kI0 _ _ h3).symm))
      m5 := fun x z h1 h2 => (kI0 _ _ h1).trans
        ((n_m5 ar ax hv x z hp1).trans (not_congr (kI0 _ _ h2).symm))
      m6 := fun x z w h1 h2 => (kI3 _ _ h1).trans ((n_m6 ar ax hv x z w hp4).trans (kI2 _ _ h2).symm)
      m7 := fun x p s r h1 h2 =>
        (kI4 _ _ h1).trans ((n_m7 ar ax hv x p s r hp5).trans (kI2 _ _ h2).symm)
      m8 := fun x p s r h1 h2 =>
        (kI4 _ _ h1).trans ((n_m8 ar ax hv x p s r hp5).trans (kI2 _ _ h2).symm)
      m9a := fun x p h1 h2 h3 a =>
        have h := n_m9a ar ax hv x p hp3 ((kI2 _ _ h1).mp a)
        ⟨(kE2 _ _ h2).mpr h.1, (kI0 _ _ h3).mpr h.2⟩
      m9b := fun x p s r h1 h2 h3 a b =>
        (kI2 _ _ h3).mpr (n_m9b ar ax hv x p s r hp3 ((kE2 _ _ h1).mp a) ((kI0 _ _ h2).mp b))
      m10a := fun x p s h1 h2 a => (kI3 _ _ h2).mpr (n_m10a ar ax hv x p s hp4 ((kI0 _ _ h1).mp a))
      m10b := fun x p h1 h2 a => (kI0 _ _ h2).mpr (n_m10b ar ax hv x p hp4 ((kI3 _ _ h1).mp a))
      m11 := fun x p s h1 h2 => (kI2 _ _ h1).trans ((n_m11 ar ax hv x p s hp3).trans (kI2 _ _ h2).symm)
      m12a := fun p h1 h2 a => (kE1 _ _ h2).mpr (n_m12a ar ax hv p hp2 ((kI1 _ _ h1).mp a))
      m12b := fun p s h1 h2 a => (kI1 _ _ h2).mpr (n_m12b ar ax hv p s hp2 ((kE1 _ _ h1).mp a))
      m13a := fun p s r h1 h2 h3 a b =>
        (kI0 _ _ h3).mpr (n_m13a ar ax hv p s r hp4 ((kI3 _ _ h1).mp a) ((kI0 _ _ h2).mp b))
      m13b := fun p s h1 h2 h3 himp => (kI3 _ _ h3).mpr
        (n_m13b ar ax hv p s hp4 (fun a => (kI0 _ _ h2).mp (himp ((kI0 _ _ h1).mpr a)))) }

end FlatM

/-! ## Phase 2 (A9): the flat model of a tower, and the sequence of all its levels -/

namespace Host

variable {H : Host}

namespace Tower

variable (T : Tower H)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
/-- **The flat model of a tower.** -/
def flat : FlatM H where
  d := T.d
  Ob := fun x a => ∃ τ G A N D, H.Rec T.F a τ G A N D ∧ x ∈ τ
  El := fun z x p => ∃ a b, p = H.op a b ∧ H.Mem T.M T.d T.F a b z x
  hd := T.hd
  defOb := by hdef
  defEl := by hdef

theorem flat_ob {x a : H.W} : T.flat.Ob x a ↔ T.Proper a ∧ x ∈ T.Tp a := by
  constructor
  · rintro ⟨τ, G, A, N, D, hr, hx⟩
    have hP := T.rec_proper hr
    rw [(T.rec_unique hP hr).1] at hx
    exact ⟨hP, hx⟩
  · rintro ⟨hP, hx⟩
    exact ⟨_, _, _, _, _, (T.spec hP).1, hx⟩

theorem flat_ob' {x a : H.W} (hP : T.Proper a) : T.flat.Ob x a ↔ x ∈ T.Tp a :=
  T.flat_ob.trans ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩

theorem flat_el {z x a b : H.W} : T.flat.El z x (H.op a b) ↔ H.Mem T.M T.d T.F a b z x := by
  constructor
  · rintro ⟨a', b', e, h⟩
    obtain ⟨e1, e2⟩ := H.op_inj e
    rw [e1, e2]
    exact h
  · exact fun h => ⟨a, b, rfl, h⟩

theorem flat_lv {a : H.W} : T.flat.Lv a ↔ T.Proper a := Iff.rfl

theorem flat_sg {a b x s : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp) :
    T.flat.IsSg a b x s ↔ T.IsSing a b x s := by
  have hb := T.lower_proper ha hba hb0
  unfold FlatM.IsSg IsSing
  rw [T.flat_ob' ha]
  exact and_congr Iff.rfl (forall_congr' fun z => by rw [T.flat_ob' hb, T.flat_el])

theorem flat_up {a b x y p : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp) :
    T.flat.IsUp a b x y p ↔ T.IsUp a b x y p := by
  have hb := T.lower_proper ha hba hb0
  unfold FlatM.IsUp IsUp
  rw [T.flat_ob' ha]
  exact and_congr Iff.rfl (forall_congr' fun z => by rw [T.flat_ob' hb, T.flat_el])

theorem flat_op {a b c x y p : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (hcb : c ∈ b) (hc0 : c ≠ H.emp) : T.flat.IsOp a b c x y p ↔ T.IsOp a b c x y p := by
  have hb := T.lower_proper ha hba hb0
  unfold FlatM.IsOp IsOp
  exact exists_congr fun s => exists_congr fun u => and_congr (T.flat_sg hb hcb hc0)
    (and_congr (T.flat_up hb hcb hc0) (T.flat_up ha hba hb0))

/-- The flat model of a tower satisfies the axioms. -/
theorem flat_ax : T.flat.Ax where
  lv_ob := fun a x h => (T.flat_ob.mp h).1
  ne := fun a ha => ⟨_, T.flat_ob.mpr ⟨ha, T.emp_mem_Tp ha⟩⟩
  ext := fun a b x y hlt hx hy h =>
    T.ext_ax hlt.1 hlt.2.1 hlt.2.2 ((T.flat_ob' hlt.1).mp hx) ((T.flat_ob' hlt.1).mp hy)
      fun z hz => (T.flat_el.symm.trans
        (h z ((T.flat_ob' (T.lower_proper hlt.1 hlt.2.1 hlt.2.2)).mpr hz))).trans T.flat_el
  sing := fun a b x hlt hx => by
    have hb := T.lower_proper hlt.1 hlt.2.1 hlt.2.2
    obtain ⟨s, hs⟩ := T.sing_ex hlt.1 hlt.2.1 hlt.2.2 ((T.flat_ob' hb).mp hx)
    exact ⟨s, (T.flat_sg hlt.1 hlt.2.1 hlt.2.2).mpr hs⟩
  up := fun a b x y hlt hx hy => by
    have hb := T.lower_proper hlt.1 hlt.2.1 hlt.2.2
    obtain ⟨p, hp⟩ := T.up_ex hlt.1 hlt.2.1 hlt.2.2 ((T.flat_ob' hb).mp hx) ((T.flat_ob' hb).mp hy)
    exact ⟨p, (T.flat_up hlt.1 hlt.2.1 hlt.2.2).mpr hp⟩
  inter := fun a b x y hlt hx hy => by
    have hb := T.lower_proper hlt.1 hlt.2.1 hlt.2.2
    obtain ⟨w, hw, h⟩ := T.inter_ex hlt.1 hlt.2.1 hlt.2.2 ((T.flat_ob' hlt.1).mp hx)
      ((T.flat_ob' hlt.1).mp hy)
    refine ⟨w, (T.flat_ob' hlt.1).mpr hw, fun z hz => ?_⟩
    rw [T.flat_el, T.flat_el, T.flat_el]
    exact h z ((T.flat_ob' hb).mp hz)
  compl := fun a b x hlt hx => by
    have hb := T.lower_proper hlt.1 hlt.2.1 hlt.2.2
    obtain ⟨w, hw, h⟩ := T.compl_ex hlt.1 hlt.2.1 hlt.2.2 ((T.flat_ob' hlt.1).mp hx)
    refine ⟨w, (T.flat_ob' hlt.1).mpr hw, fun z hz => ?_⟩
    rw [T.flat_el, T.flat_el]
    exact h z ((T.flat_ob' hb).mp hz)
  cardinalOne := fun a b c h1 h2 => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    obtain ⟨y, hy, h⟩ := T.cardinalOne_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2
    refine ⟨y, (T.flat_ob' h1.1).mpr hy, fun p hp => ?_⟩
    rw [T.flat_el]
    exact (h p ((T.flat_ob' hb).mp hp)).trans (exists_congr fun q =>
      and_congr (T.flat_ob' hc).symm (T.flat_sg hb h2.2.1 h2.2.2).symm)
  vCross := fun a b c e x h1 h2 h3 hx => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    have he := T.lower_proper hc h3.2.1 h3.2.2
    obtain ⟨y, hy, h⟩ := T.vCross_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2
      ((T.flat_ob' hc).mp hx)
    refine ⟨y, (T.flat_ob' h1.1).mpr hy, fun p hp => ?_⟩
    rw [T.flat_el]
    refine (h p ((T.flat_ob' hb).mp hp)).trans ?_
    constructor
    · rintro ⟨q, hq, r, hr, hop, hm⟩
      exact ⟨q, r, (T.flat_ob' he).mpr hq, (T.flat_ob' he).mpr hr,
        (T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mpr hop, T.flat_el.mpr hm⟩
    · rintro ⟨q, r, hq, hr, hop, hm⟩
      exact ⟨q, (T.flat_ob' he).mp hq, r, (T.flat_ob' he).mp hr,
        (T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mp hop, T.flat_el.mp hm⟩
  converse := fun a b c e x h1 h2 h3 hx => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    have he := T.lower_proper hc h3.2.1 h3.2.2
    obtain ⟨y, hy, h⟩ := T.converse_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2
      ((T.flat_ob' h1.1).mp hx)
    refine ⟨y, (T.flat_ob' h1.1).mpr hy, fun p q r r' hp hq hr hr' => ?_⟩
    rw [T.flat_el, T.flat_el]
    exact h p q r r' ((T.flat_ob' he).mp hp) ((T.flat_ob' he).mp hq)
      ((T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mp hr)
      ((T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mp hr')
  subset := fun a b c e g h1 h2 h3 h4 => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    have he := T.lower_proper hc h3.2.1 h3.2.2
    have hg := T.lower_proper he h4.2.1 h4.2.2
    obtain ⟨y, hy, h⟩ := T.subset_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2 h4.2.1 h4.2.2
    refine ⟨y, (T.flat_ob' h1.1).mpr hy, fun p q o hp hq ho => ?_⟩
    rw [T.flat_el]
    refine (h p q o ((T.flat_ob' he).mp hp) ((T.flat_ob' he).mp hq)
      ((T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mp ho)).trans ?_
    exact forall_congr' fun r => by rw [T.flat_ob' hg, T.flat_el, T.flat_el]
  singletonImage := fun a b c e g x h1 h2 h3 h4 hx => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    have he := T.lower_proper hc h3.2.1 h3.2.2
    have hg := T.lower_proper he h4.2.1 h4.2.2
    obtain ⟨y, hy, h⟩ := T.singletonImage_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2
      h4.2.1 h4.2.2 ((T.flat_ob' hb).mp hx)
    refine ⟨y, (T.flat_ob' h1.1).mpr hy, fun z w sz sw P Q hz hw hsz hsw hP hQ => ?_⟩
    rw [T.flat_el, T.flat_el]
    exact h z w sz sw P Q ((T.flat_ob' hg).mp hz) ((T.flat_ob' hg).mp hw)
      ((T.flat_sg he h4.2.1 h4.2.2).mp hsz) ((T.flat_sg he h4.2.1 h4.2.2).mp hsw)
      ((T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mp hP)
      ((T.flat_op hc h3.2.1 h3.2.2 h4.2.1 h4.2.2).mp hQ)
  insertion2 := fun a b c e g f x h1 h2 h3 h4 h5 hx => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    have he := T.lower_proper hc h3.2.1 h3.2.2
    have hg := T.lower_proper he h4.2.1 h4.2.2
    have hf := T.lower_proper hg h5.2.1 h5.2.2
    obtain ⟨y, hy, h⟩ := T.insertion2_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2
      h4.2.1 h4.2.2 h5.2.1 h5.2.2 ((T.flat_ob' hc).mp hx)
    refine ⟨y, (T.flat_ob' h1.1).mpr hy,
      fun p q r sp ssp oqr P opr hp hq hr hsp hssp hoqr hP hopr => ?_⟩
    rw [T.flat_el, T.flat_el]
    exact h p q r sp ssp oqr P opr ((T.flat_ob' hf).mp hp) ((T.flat_ob' hf).mp hq)
      ((T.flat_ob' hf).mp hr) ((T.flat_sg hg h5.2.1 h5.2.2).mp hsp)
      ((T.flat_sg he h4.2.1 h4.2.2).mp hssp)
      ((T.flat_op he h4.2.1 h4.2.2 h5.2.1 h5.2.2).mp hoqr)
      ((T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mp hP)
      ((T.flat_op he h4.2.1 h4.2.2 h5.2.1 h5.2.2).mp hopr)
  insertion3 := fun a b c e g f x h1 h2 h3 h4 h5 hx => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    have he := T.lower_proper hc h3.2.1 h3.2.2
    have hg := T.lower_proper he h4.2.1 h4.2.2
    have hf := T.lower_proper hg h5.2.1 h5.2.2
    obtain ⟨y, hy, h⟩ := T.insertion3_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2
      h4.2.1 h4.2.2 h5.2.1 h5.2.2 ((T.flat_ob' hc).mp hx)
    refine ⟨y, (T.flat_ob' h1.1).mpr hy,
      fun p q r sp ssp oqr P opq hp hq hr hsp hssp hoqr hP hopq => ?_⟩
    rw [T.flat_el, T.flat_el]
    exact h p q r sp ssp oqr P opq ((T.flat_ob' hf).mp hp) ((T.flat_ob' hf).mp hq)
      ((T.flat_ob' hf).mp hr) ((T.flat_sg hg h5.2.1 h5.2.2).mp hsp)
      ((T.flat_sg he h4.2.1 h4.2.2).mp hssp)
      ((T.flat_op he h4.2.1 h4.2.2 h5.2.1 h5.2.2).mp hoqr)
      ((T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2).mp hP)
      ((T.flat_op he h4.2.1 h4.2.2 h5.2.1 h5.2.2).mp hopq)
  typeLower := fun a b c e g x h1 h2 h3 h4 hx => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    have he := T.lower_proper hc h3.2.1 h3.2.2
    have hg := T.lower_proper he h4.2.1 h4.2.2
    obtain ⟨y, hy, h⟩ := T.typeLower_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2
      h4.2.1 h4.2.2 ((T.flat_ob' h1.1).mp hx)
    refine ⟨y, (T.flat_ob' he).mpr hy, fun p hp => ?_⟩
    rw [T.flat_el]
    refine (h p ((T.flat_ob' hg).mp hp)).trans ?_
    exact forall_congr' fun q => forall_congr' fun sp => forall_congr' fun P => by
      rw [T.flat_ob' he, T.flat_sg he h4.2.1 h4.2.2,
        T.flat_op hb h2.2.1 h2.2.2 h3.2.1 h3.2.2, T.flat_el]

end Tower

variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- The sequence `1, 2, …, l` of levels of a flat model of height at least `l`. -/
theorem exists_levels (ar : H.Arith E num) (Fm : FlatM H) {D l : N} (hd : Fm.d = num D)
    (hl : l ≤ D) : ∃ e0, H.IncSeq e0 (num l) ∧ ∀ k a, H.App e0 k a → Fm.Lv a := by
  let e0 := H.mkFun (num l) (fun x y => y = H.suc x) (by hdef)
    (fun u _ v v' h h' => h.trans h'.symm)
  have happ : ∀ {k a : H.W}, H.App e0 k a ↔ k ∈ num l ∧ a = H.suc k := H.app_mkFun
  refine ⟨e0, ⟨⟨H.isFun_mkFun, fun a => ⟨fun ha => ⟨_, happ.mpr ⟨ha, rfl⟩⟩,
    fun ⟨b, hb⟩ => (happ.mp hb).1⟩⟩, ar.num_om l, ?_, ?_⟩, ?_⟩
  · intro i a hi
    obtain ⟨h1, rfl⟩ := happ.mp hi
    exact H.suc_mem_om (H.mem_om_of_mem (ar.num_om l) h1)
  · intro i j a b hi hj hij
    obtain ⟨h1, rfl⟩ := happ.mp hi
    obtain ⟨h2, rfl⟩ := happ.mp hj
    obtain ⟨i', -, rfl⟩ := ar.mem_num.mp h1
    obtain ⟨j', -, rfl⟩ := ar.mem_num.mp h2
    rw [← ar.iso.succ, ← ar.iso.succ]
    exact ar.num_mem.mpr (ar.nf.add_le_add_r (ar.num_mem.mp hij) 1)
  · intro k a hk
    obtain ⟨h1, rfl⟩ := happ.mp hk
    obtain ⟨i', hi', rfl⟩ := ar.mem_num.mp h1
    refine ⟨?_, H.suc_ne_emp _⟩
    rw [hd, ← ar.iso.succ, ← ar.iso.succ]
    exact ar.num_mem.mpr (ar.nf.add_le_add_r (le_trans hi' hl) 1)

end Host

/-! ## Phase 2 (A10): a truth assignment that satisfies the axioms N below `q`

The combinatorial core of the existence proof, in a host whose numbers are a copy of `N` and
in which induction over `N` is available for definable relations along the functions of a
class `G` (on the side of NFU: the functions with a graph). -/

namespace Host

variable {H : Host}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

theorem def_ram : Def3 H (fun r q Q => H.Ram r q Q) := by
  have h1 := H.def_incSeq
  have h2 := H.def_card
  hdef

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **The core of the existence proof.** `Tw` is a function with `rstep (Tw n) ≤ Tw (n + 1)`.
If the flat model has at least `Tw (m + (2R + 1) q)` levels, then there is a sequence of
`Tw m` levels whose truth assignment satisfies the axioms N below `q`. -/
theorem sound_core (ar : H.Arith E num) (Fm : FlatM H) (ax : Fm.Ax) (Tw : N → N)
    (hTw : ∀ n, rstep E (Tw n) ≤ Tw (n + 1)) (G : (N → N) → Prop)
    (MI : ∀ (P : H.W → H.W → Prop), Def2 H P → ∀ g : N → N, G g → P (num 0) (num (g 0)) →
      (∀ b, P (num b) (num (g b)) → P (num (b + 1)) (num (g (b + 1)))) →
      ∀ b, P (num b) (num (g b)))
    (hG1 : ∀ a, G (fun j => Tw (a + j))) (hG2 : ∀ m r, G (fun k => Tw (m + r * k)))
    {D q R m : N} (hd : Fm.d = num D) (hrad : 5 * q + 6 ≤ R)
    (hD : Tw (m + (R + R + 1) * q) ≤ D) (hm : R + 5 + R + 1 ≤ Tw m) :
    ∃ e, H.IncSeq e (num (Tw m)) ∧ (∀ k a, H.App e k a → Fm.Lv a) ∧
      NSat (fun i => Fm.AllT ar e (num i) (num R)) q := by
  have hdr := H.def_ram
  have hdi := H.def_incSeq
  have hdt := Fm.def_tr ar
  have hdA := ar.def_Ad
  -- the Ramsey property along the tower
  have hT : ∀ a j : N, H.Ram (num j) (num (Tw a)) (num (Tw (a + j))) := by
    intro a
    refine MI (fun x y => H.Ram x (num (Tw a)) y) (by hdef) (fun j => Tw (a + j)) (hG1 a) ?_ ?_
    · show H.Ram (num 0) (num (Tw a)) (num (Tw (a + 0)))
      rw [add_zero]
      exact H.ram_zero ar _
    · intro b ih
      show H.Ram (num (b + 1)) (num (Tw a)) (num (Tw (a + (b + 1))))
      exact H.ram_step ar ih (by rw [← add_assoc]; exact hTw _)
  -- deciding the atoms one after the other
  have hS : ∀ k : N, (num k ∈ num q ∨ num k = num q) → ∀ e', H.IncSeq e' (num (Tw (m + (R + R + 1) * k))) →
      ∃ e, H.IncSeq e (num (Tw m)) ∧ H.SubSeq e e' ∧ ∀ i, i ∈ num k →
        (Fm.AllT ar e i (num R) ∨ Fm.AllF ar e i (num R)) := by
    refine MI (fun x y => (x ∈ num q ∨ x = num q) → ∀ e', H.IncSeq e' y →
      ∃ e, H.IncSeq e (num (Tw m)) ∧ H.SubSeq e e' ∧ ∀ i, i ∈ x →
        (Fm.AllT ar e i (num R) ∨ Fm.AllF ar e i (num R))) (by hdef)
      (fun k => Tw (m + (R + R + 1) * k)) (hG2 m (R + R + 1)) ?_ ?_
    · intro _ e' he'
      rw [show m + (R + R + 1) * 0 = m from by ring] at he'
      refine ⟨e', he', fun i a h => ⟨i, h⟩, fun i hi => ?_⟩
      rw [ar.iso.zero] at hi
      exact (H.not_mem_emp i hi).elim
    · intro b ih hb e' he'
      have hbq : b + 1 ≤ q := ar.num_le.mp hb
      obtain ⟨c, hc⟩ := (ar.nf.le_iff _ _).mp hbq
      have hbR : 5 * b + 6 ≤ R :=
        le_trans ((ar.nf.le_iff _ _).mpr ⟨5 * c + 5, by rw [← hc]; ring⟩) hrad
      rw [show m + (R + R + 1) * (b + 1) = m + (R + R + 1) * b + (R + R + 1) from by ring] at he'
      obtain ⟨e1, he1, he1e', hdec1⟩ := FlatM.decide_atom (Fm := Fm) ar hbR he' (hT _ _)
      obtain ⟨e, he, hee1, hdec⟩ := ih (ar.num_le.mpr (le_trans (ar.nf.le_add b 1) hbq)) e1 he1
      refine ⟨e, he, hee1.trans he1e', fun i hi => ?_⟩
      rw [ar.iso.succ] at hi
      rcases H.mem_suc.mp hi with h | h
      · exact hdec i h
      · rw [h]
        rcases hdec1 with h1 | h1
        · exact Or.inl (h1.sub hee1)
        · exact Or.inr (h1.sub hee1)
  obtain ⟨e0, he0, hlv0⟩ := H.exists_levels ar Fm hd hD
  obtain ⟨e, he, hee0, hdec⟩ := hS q (Or.inr rfl) e0 he0
  have hlv : ∀ k a, H.App e k a → Fm.Lv a := fun k a hk => by
    obtain ⟨j, hj⟩ := hee0 k a hk
    exact hlv0 j a hj
  exact ⟨e, he, hlv, FlatM.nsat_of_dec ar ax he hlv hm
    (fun i hi => hdec (num i) (ar.num_mem.mpr hi))⟩

end Host

/-! ## Phase 2: the satisfaction of the axioms N depends only on the atoms below the bound

Generated (see `gen/gen53.py` for the list of the axioms). -/

namespace NSat

variable {N : Type} [CommSemiring N] [PartialOrder N] {τ τ' : N → Prop} {q q' : N}

/-- Two truth assignments that agree below `q` satisfy the same instances below `q`. -/
theorem congr (hag : ∀ i : N, i + 1 ≤ q → (τ i ↔ τ' i)) (h : NSat τ q) : NSat τ' q where
  e1 := fun x h1 => by
    rw [← hag _ h1]
    exact h.e1 x h1
  e2 := fun x y z h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.e2 x y z h1 h2 h3
  e3 := fun x x' y y' h1 h2 h3 h4 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3, ← hag _ h4]
    exact h.e3 x x' y y' h1 h2 h3 h4
  e4a := fun x x' h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.e4a x x' h1 h2
  e4b := fun x x' y y' h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.e4b x x' y y' h1 h2 h3
  m1 := fun x y h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.m1 x y h1 h2 h3
  m2 := fun x y h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m2 x y h1 h2
  m3 := fun x y z h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.m3 x y z h1 h2 h3
  m4 := fun x y z h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.m4 x y z h1 h2 h3
  m5 := fun x z h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m5 x z h1 h2
  m6 := fun x z w h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m6 x z w h1 h2
  m7 := fun x p s r h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m7 x p s r h1 h2
  m8 := fun x p s r h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m8 x p s r h1 h2
  m9a := fun x p h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.m9a x p h1 h2 h3
  m9b := fun x p s r h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.m9b x p s r h1 h2 h3
  m10a := fun x p s h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m10a x p s h1 h2
  m10b := fun x p h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m10b x p h1 h2
  m11 := fun x p s h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m11 x p s h1 h2
  m12a := fun p h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m12a p h1 h2
  m12b := fun p s h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.m12b p s h1 h2
  m13a := fun p s r h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.m13a p s r h1 h2 h3
  m13b := fun p s h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.m13b p s h1 h2 h3

/-- Satisfaction below `q` implies satisfaction below every smaller bound. -/
theorem mono (hqq : q' ≤ q) (h : NSat τ q) : NSat τ q' where
  e1 := fun x h1 => h.e1 x (le_trans h1 hqq)
  e2 := fun x y z h1 h2 h3 => h.e2 x y z (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  e3 := fun x x' y y' h1 h2 h3 h4 => h.e3 x x' y y' (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq) (le_trans h4 hqq)
  e4a := fun x x' h1 h2 => h.e4a x x' (le_trans h1 hqq) (le_trans h2 hqq)
  e4b := fun x x' y y' h1 h2 h3 => h.e4b x x' y y' (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  m1 := fun x y h1 h2 h3 => h.m1 x y (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  m2 := fun x y h1 h2 => h.m2 x y (le_trans h1 hqq) (le_trans h2 hqq)
  m3 := fun x y z h1 h2 h3 => h.m3 x y z (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  m4 := fun x y z h1 h2 h3 => h.m4 x y z (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  m5 := fun x z h1 h2 => h.m5 x z (le_trans h1 hqq) (le_trans h2 hqq)
  m6 := fun x z w h1 h2 => h.m6 x z w (le_trans h1 hqq) (le_trans h2 hqq)
  m7 := fun x p s r h1 h2 => h.m7 x p s r (le_trans h1 hqq) (le_trans h2 hqq)
  m8 := fun x p s r h1 h2 => h.m8 x p s r (le_trans h1 hqq) (le_trans h2 hqq)
  m9a := fun x p h1 h2 h3 => h.m9a x p (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  m9b := fun x p s r h1 h2 h3 => h.m9b x p s r (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  m10a := fun x p s h1 h2 => h.m10a x p s (le_trans h1 hqq) (le_trans h2 hqq)
  m10b := fun x p h1 h2 => h.m10b x p (le_trans h1 hqq) (le_trans h2 hqq)
  m11 := fun x p s h1 h2 => h.m11 x p s (le_trans h1 hqq) (le_trans h2 hqq)
  m12a := fun p h1 h2 => h.m12a p (le_trans h1 hqq) (le_trans h2 hqq)
  m12b := fun p s h1 h2 => h.m12b p s (le_trans h1 hqq) (le_trans h2 hqq)
  m13a := fun p s r h1 h2 h3 => h.m13a p s r (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  m13b := fun p s h1 h2 h3 => h.m13b p s (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)

end NSat

