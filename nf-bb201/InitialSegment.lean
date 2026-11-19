import Std

/-!
A finite arithmetic seed for the NF201 argument. A coded chart supplies a
structure satisfying these elementary clauses and an interpreted consistency
sentence. Every bounded verifier on ordinary numeral inputs has the same truth
value in the two arithmetics. No induction axiom inside the target is used.
-/
namespace NF201.InitialSegment

structure Arithmetic (A : Type u) where
  zero : A
  succ : A → A
  add : A → A → A
  mul : A → A → A
  lt : A → A → Prop
  zero_ne_succ : ∀ x, zero ≠ succ x
  succ_injective : ∀ {x y}, succ x = succ y → x = y
  add_zero : ∀ x, add x zero = x
  add_succ : ∀ x y, add x (succ y) = succ (add x y)
  mul_zero : ∀ x, mul x zero = zero
  mul_succ : ∀ x y, mul x (succ y) = add (mul x y) x
  not_lt_zero : ∀ x, ¬ lt x zero
  lt_succ : ∀ x y, lt x (succ y) ↔ lt x y ∨ x = y

def standard : Arithmetic Nat where
  zero := 0
  succ := Nat.succ
  add := Nat.add
  mul := Nat.mul
  lt := Nat.lt
  zero_ne_succ := fun _ h => Nat.noConfusion h
  succ_injective := Nat.succ.inj
  add_zero := Nat.add_zero
  add_succ := Nat.add_succ
  mul_zero := Nat.mul_zero
  mul_succ := Nat.mul_succ
  not_lt_zero := Nat.not_lt_zero
  lt_succ := fun _ _ => Nat.lt_succ_iff_lt_or_eq

variable {A : Type u} (M : Arithmetic A)

def numeral : Nat → A
  | 0 => M.zero
  | n + 1 => M.succ (numeral n)

theorem numeral_injective {m n : Nat} (eq : numeral M m = numeral M n) : m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => exact (M.zero_ne_succ _ eq).elim
  | succ m ih =>
    cases n with
    | zero => exact (M.zero_ne_succ _ eq.symm).elim
    | succ n => exact congrArg Nat.succ (ih (M.succ_injective eq))

theorem numeral_add (m n : Nat) : M.add (numeral M m) (numeral M n) = numeral M (m+n) := by
  induction n with
  | zero => exact M.add_zero _
  | succ n ih => exact (M.add_succ _ _).trans (congrArg M.succ ih)

theorem numeral_mul (m n : Nat) : M.mul (numeral M m) (numeral M n) = numeral M (m*n) := by
  induction n with
  | zero => exact M.mul_zero _
  | succ n ih =>
    rw [Nat.mul_succ]
    change M.mul _ (M.succ _) = _
    rw [M.mul_succ, ih, numeral_add]

/-- Every element below a numeral is the numeral of a smaller natural. -/
theorem below_numeral (x : A) (n : Nat) :
    M.lt x (numeral M n) ↔ ∃ j, j < n ∧ x = numeral M j := by
  induction n with
  | zero =>
    constructor
    · intro h; exact (M.not_lt_zero x h).elim
    · rintro ⟨j,h,_⟩; exact (Nat.not_lt_zero j h).elim
  | succ n ih =>
    constructor
    · intro hx
      obtain h | e := (M.lt_succ x (numeral M n)).mp hx
      · obtain ⟨j,hj,ej⟩ := ih.mp h
        exact ⟨j,Nat.lt_trans hj (Nat.lt_succ_self n),ej⟩
      · exact ⟨n,Nat.lt_succ_self n,e⟩
    · rintro ⟨j,h,e⟩
      apply (M.lt_succ x (numeral M n)).mpr
      obtain hj | eq := Nat.lt_succ_iff_lt_or_eq.mp h
      · exact Or.inl (ih.mpr ⟨j,hj,e⟩)
      · exact Or.inr (eq ▸ e)

theorem numeral_lt (m n : Nat) : M.lt (numeral M m) (numeral M n) ↔ m < n := by
  apply Iff.trans (below_numeral M _ _) _
  constructor
  · rintro ⟨j,h,e⟩; exact numeral_injective M e ▸ h
  · intro h; exact ⟨m,h,rfl⟩

inductive Term where
  | var (i : Nat) | zero | succ (t : Term) | add (s t : Term) | mul (s t : Term)

def Term.eval {A : Type u} (M : Arithmetic A) (e : Nat → A) : Term → A
  | .var i => e i
  | .zero => M.zero
  | .succ t => M.succ (eval M e t)
  | .add s t => M.add (eval M e s) (eval M e t)
  | .mul s t => M.mul (eval M e s) (eval M e t)

theorem term_transfer (t : Term) (e : Nat → Nat) (v : Nat → A)
    (agree : ∀ i, v i = numeral M (e i)) :
    t.eval M v = numeral M (t.eval standard e) := by
  induction t with
  | var i => exact agree i
  | zero => rfl
  | succ t ih => exact congrArg M.succ ih
  | add s t hs ht =>
    change M.add _ _ = _
    rw [hs, ht]; exact numeral_add M _ _
  | mul s t hs ht =>
    change M.mul _ _ = _
    rw [hs, ht]; exact numeral_mul M _ _

/-- Bounds do not bind in themselves. Bound variables use de Bruijn index 0. -/
inductive Bounded where
  | eq (s t : Term) | lt (s t : Term) | neg (p : Bounded) | conj (p q : Bounded)
  | allLt (b : Term) (p : Bounded) | exLt (b : Term) (p : Bounded)

def extend {A : Type u} (a : A) (e : Nat → A) : Nat → A
  | 0 => a
  | n+1 => e n

def Bounded.sat {A : Type u} (M : Arithmetic A) : Bounded → (Nat → A) → Prop
  | .eq s t, e => s.eval M e = t.eval M e
  | .lt s t, e => M.lt (s.eval M e) (t.eval M e)
  | .neg p, e => ¬p.sat M e
  | .conj p q, e => p.sat M e ∧ q.sat M e
  | .allLt b p, e => ∀ x, M.lt x (b.eval M e) → p.sat M (extend x e)
  | .exLt b p, e => ∃ x, M.lt x (b.eval M e) ∧ p.sat M (extend x e)

private theorem extend_agree (j : Nat) (e : Nat → Nat) (v : Nat → A)
    (agree : ∀ i, v i = numeral M (e i)) :
    ∀ i, extend (numeral M j) v i = numeral M (extend j e i) := by
  intro i
  cases i with
  | zero => rfl
  | succ i => exact agree i

/-- Pointwise agreement of environments suffices, including under a binder. -/
theorem bounded_transfer_aux (p : Bounded) (e : Nat → Nat) (v : Nat → A)
    (agree : ∀ i, v i = numeral M (e i)) :
    p.sat M v ↔ p.sat standard e := by
  induction p generalizing e v with
  | eq s t =>
    change s.eval M v = t.eval M v ↔ _
    rw [term_transfer M s e v agree, term_transfer M t e v agree]
    exact ⟨numeral_injective M, congrArg (numeral M)⟩
  | lt s t =>
    change M.lt (s.eval M v) (t.eval M v) ↔ _
    rw [term_transfer M s e v agree, term_transfer M t e v agree]
    exact numeral_lt M _ _
  | neg p ih =>
    exact ⟨fun hn h => hn ((ih e v agree).mpr h), fun hn h => hn ((ih e v agree).mp h)⟩
  | conj p q hp hq =>
    exact ⟨fun ⟨h,k⟩ => ⟨(hp e v agree).mp h,(hq e v agree).mp k⟩,
           fun ⟨h,k⟩ => ⟨(hp e v agree).mpr h,(hq e v agree).mpr k⟩⟩
  | allLt b p ih =>
    constructor
    · intro h j hj
      have hj' := (numeral_lt M j (b.eval standard e)).mpr hj
      rw [← term_transfer M b e v agree] at hj'
      exact (ih _ _ (extend_agree M j e v agree)).mp (h _ hj')
    · intro h x hx
      rw [term_transfer M b e v agree] at hx
      obtain ⟨j,hj,rfl⟩ := (below_numeral M _ _).mp hx
      exact (ih _ _ (extend_agree M j e v agree)).mpr (h j hj)
  | exLt b p ih =>
    constructor
    · rintro ⟨x,hx,hp⟩
      rw [term_transfer M b e v agree] at hx
      obtain ⟨j,hj,rfl⟩ := (below_numeral M _ _).mp hx
      exact ⟨j,hj,(ih _ _ (extend_agree M j e v agree)).mp hp⟩
    · rintro ⟨j,hj,hp⟩
      have hj' := (numeral_lt M j (b.eval standard e)).mpr hj
      rw [← term_transfer M b e v agree] at hj'
      exact ⟨numeral M j,hj',(ih _ _ (extend_agree M j e v agree)).mpr hp⟩

/-- Bounded formulas agree, including both quantifiers over a numeral bound. -/
theorem bounded_transfer (p : Bounded) (e : Nat → Nat) :
    p.sat M (numeral M ∘ e) ↔ p.sat standard e :=
  bounded_transfer_aux M p e _ (fun _ => rfl)

/-- A fixed Σ₁ verifier with extra number parameters transfers positively. -/
theorem sigma_one_upward (p : Bounded) (e : Nat → Nat)
    (h : ∃ w, p.sat standard (extend w e)) :
    ∃ w, p.sat M (extend w (numeral M ∘ e)) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨numeral M w, ?_⟩
  exact (bounded_transfer_aux M p _ _ (extend_agree M w e _ (fun _ => rfl))).mpr hw

end NF201.InitialSegment

#print axioms NF201.InitialSegment.below_numeral
#print axioms NF201.InitialSegment.bounded_transfer
#print axioms NF201.InitialSegment.sigma_one_upward
