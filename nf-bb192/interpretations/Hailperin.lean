module

public import ConNF.NF.NFModel

/-!
# Hailperin's theorem (new file)

We show that the finitely many axioms of `NFModel` imply every instance of stratified
comprehension. Formulas are in de Bruijn form with a type at each quantifier; a formula is
stratified in a context of types if `x ∈ y` only occurs with `type y = type x + 1` and `x = y`
only with `type x = type y`.

## Main statements

* `ConNF.NF.NFModel.comprehension`: stratified comprehension in every `NFModel`.
* `ConNF.NF.NFModel.isNF`: every `NFModel` satisfies extensionality and stratified comprehension.

This file imports only `ConNF.NF.NFModel` and, through it, Mathlib. That such a structure exists
is `ConNF.NF.exists_nf`, in `ConNF.NF.ExistsNF`.

## Method

In a model, sets of pairs are closed under the usual operations of the calculus of relations
(first part of the file). An assignment of values to the variables of a context is coded by a
single element: a right-nested tuple of the values, each raised by iterated singletons to the
level of the rest of the tuple. For each stratified formula, the set of codes of the assignments
that satisfy it exists, by induction on the formula.
-/

@[expose] public noncomputable section

namespace ConNF.NF

namespace NFModel

variable {V : Type} (M : NFModel V)

/-! ## Singletons and pairs -/

theorem sing_inj {a b : V} (h : M.sing a = M.sing b) : a = b := by
  have h1 : M.mem a (M.sing b) := by
    rw [← h]
    exact (M.mem_sing a a).mpr rfl
  exact (M.mem_sing b a).mp h1

theorem up_right_inj {a b d : V} (h : M.up a b = M.up a d) : b = d := by
  have hb : M.mem b (M.up a d) := by
    rw [← h]
    exact (M.mem_up a b b).mpr (Or.inr rfl)
  have hd : M.mem d (M.up a b) := by
    rw [h]
    exact (M.mem_up a d d).mpr (Or.inr rfl)
  rcases (M.mem_up a d b).mp hb with h1 | h1
  · rcases (M.mem_up a b d).mp hd with h2 | h2
    · rw [h1, h2]
    · exact h2.symm
  · exact h1

theorem op_inj {a b c d : V} (h : M.op a b = M.op c d) : a = c ∧ b = d := by
  have h' : M.up (M.sing a) (M.up a b) = M.up (M.sing c) (M.up c d) := h
  have hac : a = c := by
    have h1 : M.mem (M.sing a) (M.up (M.sing c) (M.up c d)) := by
      rw [← h']
      exact (M.mem_up _ _ _).mpr (Or.inl rfl)
    rcases (M.mem_up _ _ _).mp h1 with h2 | h2
    · exact M.sing_inj h2
    · have h3 : M.mem c (M.sing a) := by
        rw [h2]
        exact (M.mem_up _ _ _).mpr (Or.inl rfl)
      exact ((M.mem_sing a c).mp h3).symm
  subst hac
  refine ⟨rfl, ?_⟩
  have h1 : M.mem (M.up a b) (M.up (M.sing a) (M.up a d)) := by
    rw [← h']
    exact (M.mem_up _ _ _).mpr (Or.inr rfl)
  have h2 : M.mem (M.up a d) (M.up (M.sing a) (M.up a b)) := by
    rw [h']
    exact (M.mem_up _ _ _).mpr (Or.inr rfl)
  rcases (M.mem_up _ _ _).mp h1 with e1 | e1
  · rcases (M.mem_up _ _ _).mp h2 with e2 | e2
    · have hb : M.mem b (M.sing a) := by
        rw [← e1]
        exact (M.mem_up _ _ _).mpr (Or.inr rfl)
      have hd : M.mem d (M.sing a) := by
        rw [← e2]
        exact (M.mem_up _ _ _).mpr (Or.inr rfl)
      rw [(M.mem_sing a b).mp hb, (M.mem_sing a d).mp hd]
    · exact (M.up_right_inj e2).symm
  · exact M.up_right_inj e1

/-! ## Boolean operations -/

def int (x y : V) : V := (M.inter x y).choose

theorem mem_int {x y z : V} : M.mem z (M.int x y) ↔ M.mem z x ∧ M.mem z y :=
  (M.inter x y).choose_spec z

def cmp (x : V) : V := (M.compl x).choose

theorem mem_cmp {x z : V} : M.mem z (M.cmp x) ↔ ¬M.mem z x :=
  (M.compl x).choose_spec z

/-- The set of all singletons. -/
def one : V := M.cardinalOne.choose

theorem mem_one {p : V} : M.mem p M.one ↔ ∃ q, p = M.sing q :=
  M.cardinalOne.choose_spec p

def emp : V := M.int M.one (M.cmp M.one)

theorem not_mem_emp {z : V} : ¬M.mem z M.emp := fun h =>
  (M.mem_cmp.mp (M.mem_int.mp h).2) (M.mem_int.mp h).1

def univ : V := M.cmp M.emp

theorem mem_univ {z : V} : M.mem z M.univ := M.mem_cmp.mpr M.not_mem_emp

def diff (x y : V) : V := M.int x (M.cmp y)

theorem mem_diff {x y z : V} : M.mem z (M.diff x y) ↔ M.mem z x ∧ ¬M.mem z y := by
  rw [diff, mem_int, mem_cmp]

/-! ## Products and converse -/

/-- `V × x`. -/
def vx (x : V) : V := (M.vCross x).choose

theorem mem_vx {x p : V} : M.mem p (M.vx x) ↔ ∃ q r, p = M.op q r ∧ M.mem r x :=
  (M.vCross x).choose_spec p

def cv (x : V) : V := (M.converse x).choose

theorem mem_cv {x p q : V} : M.mem (M.op p q) (M.cv x) ↔ M.mem (M.op q p) x :=
  (M.converse x).choose_spec p q

/-- The set of all ordered pairs. -/
def pairs : V := M.vx M.univ

theorem mem_pairs {p : V} : M.mem p M.pairs ↔ ∃ q r, p = M.op q r := by
  rw [pairs, mem_vx]
  constructor
  · rintro ⟨q, r, h, -⟩
    exact ⟨q, r, h⟩
  · rintro ⟨q, r, h⟩
    exact ⟨q, r, h, M.mem_univ⟩

/-- The converse of a relation; it consists of pairs only. -/
def conv (x : V) : V := M.int (M.cv x) M.pairs

theorem mem_conv {x p : V} :
    M.mem p (M.conv x) ↔ ∃ q r, p = M.op q r ∧ M.mem (M.op r q) x := by
  rw [conv, mem_int, mem_pairs]
  constructor
  · rintro ⟨h, q, r, rfl⟩
    exact ⟨q, r, rfl, M.mem_cv.mp h⟩
  · rintro ⟨q, r, rfl, h⟩
    exact ⟨M.mem_cv.mpr h, q, r, rfl⟩

theorem mem_conv_op {x q r : V} : M.mem (M.op q r) (M.conv x) ↔ M.mem (M.op r q) x := by
  rw [mem_conv]
  constructor
  · rintro ⟨q', r', h, hx⟩
    obtain ⟨rfl, rfl⟩ := M.op_inj h
    exact hx
  · intro h
    exact ⟨q, r, rfl, h⟩

/-- `a × V`. -/
def xv (a : V) : V := M.conv (M.vx a)

theorem mem_xv {a p : V} : M.mem p (M.xv a) ↔ ∃ q r, p = M.op q r ∧ M.mem q a := by
  rw [xv, mem_conv]
  constructor
  · rintro ⟨q, r, rfl, h⟩
    obtain ⟨q', r', h', ha⟩ := M.mem_vx.mp h
    obtain ⟨-, rfl⟩ := M.op_inj h'
    exact ⟨_, _, rfl, ha⟩
  · rintro ⟨q, r, rfl, h⟩
    exact ⟨q, r, rfl, M.mem_vx.mpr ⟨r, q, rfl, h⟩⟩

/-- `a × b`. -/
def prod (a b : V) : V := M.int (M.xv a) (M.vx b)

theorem mem_prod {a b p : V} :
    M.mem p (M.prod a b) ↔ ∃ q r, p = M.op q r ∧ M.mem q a ∧ M.mem r b := by
  rw [prod, mem_int, mem_xv, mem_vx]
  constructor
  · rintro ⟨⟨q, r, rfl, hq⟩, q', r', h, hr⟩
    obtain ⟨-, rfl⟩ := M.op_inj h
    exact ⟨_, _, rfl, hq, hr⟩
  · rintro ⟨q, r, rfl, hq, hr⟩
    exact ⟨⟨q, r, rfl, hq⟩, q, r, rfl, hr⟩

/-! ## Singleton image, range, domain -/

def si (x : V) : V := (M.singletonImage x).choose

theorem mem_si {x z w : V} :
    M.mem (M.op (M.sing z) (M.sing w)) (M.si x) ↔ M.mem (M.op z w) x :=
  (M.singletonImage x).choose_spec z w

/-- The singleton image of a relation: `{⟨{z}, {w}⟩ | ⟨z, w⟩ ∈ x}`, and nothing else. -/
def SI (x : V) : V := M.int (M.si x) (M.prod M.one M.one)

theorem mem_SI {x p : V} :
    M.mem p (M.SI x) ↔ ∃ z w, p = M.op (M.sing z) (M.sing w) ∧ M.mem (M.op z w) x := by
  rw [SI, mem_int, mem_prod]
  constructor
  · rintro ⟨h, q, r, rfl, hq, hr⟩
    obtain ⟨z, rfl⟩ := M.mem_one.mp hq
    obtain ⟨w, rfl⟩ := M.mem_one.mp hr
    exact ⟨z, w, rfl, M.mem_si.mp h⟩
  · rintro ⟨z, w, rfl, h⟩
    exact ⟨M.mem_si.mpr h, _, _, rfl, M.mem_one.mpr ⟨z, rfl⟩, M.mem_one.mpr ⟨w, rfl⟩⟩

def tl (x : V) : V := (M.typeLower x).choose

theorem mem_tl {x p : V} : M.mem p (M.tl x) ↔ ∀ q, M.mem (M.op q (M.sing p)) x :=
  (M.typeLower x).choose_spec p

/-- The range of a relation. -/
def rng (x : V) : V := M.cmp (M.tl (M.cmp (M.SI x)))

theorem mem_rng {x p : V} : M.mem p (M.rng x) ↔ ∃ z, M.mem (M.op z p) x := by
  rw [rng, mem_cmp, mem_tl, not_forall]
  constructor
  · rintro ⟨q, hq⟩
    rw [mem_cmp, not_not, mem_SI] at hq
    obtain ⟨z, w, h, hx⟩ := hq
    obtain ⟨-, hw⟩ := M.op_inj h
    rw [M.sing_inj hw]
    exact ⟨z, hx⟩
  · rintro ⟨z, hz⟩
    refine ⟨M.sing z, ?_⟩
    rw [mem_cmp, not_not, mem_SI]
    exact ⟨z, p, rfl, hz⟩

/-- The domain of a relation. -/
def dom (x : V) : V := M.rng (M.conv x)

theorem mem_dom {x p : V} : M.mem p (M.dom x) ↔ ∃ z, M.mem (M.op p z) x := by
  rw [dom, mem_rng]
  simp only [mem_conv_op]

/-- The image of a set under the singleton map. -/
def simg (a : V) : V := M.rng (M.SI (M.vx a))

theorem mem_simg {a p : V} : M.mem p (M.simg a) ↔ ∃ w, p = M.sing w ∧ M.mem w a := by
  rw [simg, mem_rng]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z', w, h, hx⟩ := M.mem_SI.mp hz
    obtain ⟨-, rfl⟩ := M.op_inj h
    obtain ⟨q, r, h', hr⟩ := M.mem_vx.mp hx
    obtain ⟨-, rfl⟩ := M.op_inj h'
    exact ⟨_, rfl, hr⟩
  · rintro ⟨w, rfl, hw⟩
    exact ⟨M.sing w, M.mem_SI.mpr ⟨w, w, rfl, M.mem_vx.mpr ⟨w, w, rfl, hw⟩⟩⟩

/-- The preimage of a set under the singleton map. -/
def unsing (a : V) : V := M.tl (M.vx a)

theorem mem_unsing {a p : V} : M.mem p (M.unsing a) ↔ M.mem (M.sing p) a := by
  rw [unsing, mem_tl]
  constructor
  · intro h
    obtain ⟨q, r, h', hr⟩ := M.mem_vx.mp (h p)
    obtain ⟨-, rfl⟩ := M.op_inj h'
    exact hr
  · intro h q
    exact M.mem_vx.mpr ⟨q, _, rfl, h⟩

/-! ## Identity and membership relations -/

def sub : V := M.subset.choose

theorem mem_sub {p q : V} : M.mem (M.op p q) M.sub ↔ ∀ r, M.mem r p → M.mem r q :=
  M.subset.choose_spec p q

/-- The identity relation. -/
def idr : V := M.int (M.int M.sub M.pairs) (M.conv M.sub)

theorem mem_idr {p : V} : M.mem p M.idr ↔ ∃ a, p = M.op a a := by
  rw [idr, mem_int, mem_int, mem_pairs, mem_conv]
  constructor
  · rintro ⟨⟨h1, q, r, rfl⟩, q', r', h, h2⟩
    obtain ⟨rfl, rfl⟩ := M.op_inj h
    have hqr := M.ext _ _ fun z => ⟨M.mem_sub.mp h1 z, M.mem_sub.mp h2 z⟩
    rw [hqr]
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨M.mem_sub.mpr fun _ h => h, a, a, rfl⟩, a, a, rfl, M.mem_sub.mpr fun _ h => h⟩

/-- The membership relation `{⟨{x}, y⟩ | x ∈ y}`. -/
def E0 : V := M.int M.sub (M.prod M.one M.univ)

theorem mem_E0 {p : V} : M.mem p M.E0 ↔ ∃ x y, p = M.op (M.sing x) y ∧ M.mem x y := by
  rw [E0, mem_int, mem_prod]
  constructor
  · rintro ⟨h1, q, r, rfl, hq, -⟩
    obtain ⟨x, rfl⟩ := M.mem_one.mp hq
    exact ⟨x, r, rfl, M.mem_sub.mp h1 x ((M.mem_sing x x).mpr rfl)⟩
  · rintro ⟨x, y, rfl, hxy⟩
    refine ⟨M.mem_sub.mpr fun r hr => ?_, _, _, rfl, M.mem_one.mpr ⟨x, rfl⟩, M.mem_univ⟩
    rw [(M.mem_sing x r).mp hr]
    exact hxy

/-! ## Triples and relative product -/

/-- The set of all triples `⟨{{a}}, ⟨b, c⟩⟩`. -/
def tri : V := M.prod (M.simg M.one) M.pairs

theorem mem_tri {p : V} :
    M.mem p M.tri ↔ ∃ a b c, p = M.op (M.sing (M.sing a)) (M.op b c) := by
  rw [tri, mem_prod]
  constructor
  · rintro ⟨q, r, rfl, hq, hr⟩
    obtain ⟨w, rfl, hw⟩ := M.mem_simg.mp hq
    obtain ⟨a, rfl⟩ := M.mem_one.mp hw
    obtain ⟨b, c, rfl⟩ := M.mem_pairs.mp hr
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨_, _, rfl, M.mem_simg.mpr ⟨_, rfl, M.mem_one.mpr ⟨a, rfl⟩⟩,
      M.mem_pairs.mpr ⟨b, c, rfl⟩⟩

def i2 (x : V) : V := (M.insertion2 x).choose

theorem mem_i2 {x p q r : V} :
    M.mem (M.op (M.sing (M.sing p)) (M.op q r)) (M.i2 x) ↔ M.mem (M.op p r) x :=
  (M.insertion2 x).choose_spec p q r

/-- `{⟨{{a}}, ⟨b, c⟩⟩ | ⟨a, c⟩ ∈ x}`, and nothing else. -/
def I2 (x : V) : V := M.int (M.i2 x) M.tri

theorem mem_I2 {x p : V} : M.mem p (M.I2 x) ↔
    ∃ a b c, p = M.op (M.sing (M.sing a)) (M.op b c) ∧ M.mem (M.op a c) x := by
  rw [I2, mem_int, mem_tri]
  constructor
  · rintro ⟨h, a, b, c, rfl⟩
    exact ⟨a, b, c, rfl, M.mem_i2.mp h⟩
  · rintro ⟨a, b, c, rfl, h⟩
    exact ⟨M.mem_i2.mpr h, a, b, c, rfl⟩

def i3 (x : V) : V := (M.insertion3 x).choose

theorem mem_i3 {x p q r : V} :
    M.mem (M.op (M.sing (M.sing p)) (M.op q r)) (M.i3 x) ↔ M.mem (M.op p q) x :=
  (M.insertion3 x).choose_spec p q r

/-- `{⟨{{a}}, ⟨b, c⟩⟩ | ⟨a, b⟩ ∈ x}`, and nothing else. -/
def I3 (x : V) : V := M.int (M.i3 x) M.tri

theorem mem_I3 {x p : V} : M.mem p (M.I3 x) ↔
    ∃ a b c, p = M.op (M.sing (M.sing a)) (M.op b c) ∧ M.mem (M.op a b) x := by
  rw [I3, mem_int, mem_tri]
  constructor
  · rintro ⟨h, a, b, c, rfl⟩
    exact ⟨a, b, c, rfl, M.mem_i3.mp h⟩
  · rintro ⟨a, b, c, rfl, h⟩
    exact ⟨M.mem_i3.mpr h, a, b, c, rfl⟩

/-- The relative product of two relations. -/
def comp (R S : V) : V := M.rng (M.int (M.I3 (M.conv R)) (M.I2 S))

theorem mem_comp {R S p : V} : M.mem p (M.comp R S) ↔
    ∃ b a c, p = M.op b c ∧ M.mem (M.op b a) R ∧ M.mem (M.op a c) S := by
  rw [comp, mem_rng]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨h3, h2⟩ := M.mem_int.mp hz
    obtain ⟨a, b, c, h, hR⟩ := M.mem_I3.mp h3
    obtain ⟨a', b', c', h', hS⟩ := M.mem_I2.mp h2
    obtain ⟨hz1, hp1⟩ := M.op_inj h
    obtain ⟨hz2, hp2⟩ := M.op_inj h'
    have haa : a = a' := M.sing_inj (M.sing_inj (hz1.symm.trans hz2))
    obtain ⟨hbb, hcc⟩ := M.op_inj (hp1.symm.trans hp2)
    subst haa hbb hcc
    exact ⟨b, a, c, hp1, M.mem_conv_op.mp hR, hS⟩
  · rintro ⟨b, a, c, rfl, hR, hS⟩
    exact ⟨M.sing (M.sing a), M.mem_int.mpr
      ⟨M.mem_I3.mpr ⟨a, b, c, rfl, M.mem_conv_op.mpr hR⟩, M.mem_I2.mpr ⟨a, b, c, rfl, hS⟩⟩⟩

/-! ## Iterated singletons -/

/-- The `k`-fold singleton. -/
def isg (k : ℕ) (a : V) : V := (M.sing)^[k] a

theorem isg_zero (a : V) : M.isg 0 a = a := rfl

theorem isg_succ (k : ℕ) (a : V) : M.isg (k + 1) a = M.sing (M.isg k a) :=
  Function.iterate_succ_apply' _ _ _

theorem isg_succ' (k : ℕ) (a : V) : M.isg (k + 1) a = M.isg k (M.sing a) :=
  Function.iterate_succ_apply _ _ _

theorem isg_inj {k : ℕ} {a b : V} (h : M.isg k a = M.isg k b) : a = b := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [isg_succ, isg_succ] at h
    exact ih (M.sing_inj h)

/-- The image of a set under the `k`-fold singleton map. -/
def simgN (k : ℕ) (a : V) : V := (M.simg)^[k] a

theorem simgN_succ (k : ℕ) (a : V) : M.simgN (k + 1) a = M.simg (M.simgN k a) :=
  Function.iterate_succ_apply' _ _ _

theorem mem_simgN {k : ℕ} {a p : V} :
    M.mem p (M.simgN k a) ↔ ∃ w, p = M.isg k w ∧ M.mem w a := by
  induction k generalizing p with
  | zero =>
    constructor
    · intro h
      exact ⟨p, rfl, h⟩
    · rintro ⟨w, rfl, h⟩
      exact h
  | succ k ih =>
    rw [simgN_succ, mem_simg]
    constructor
    · rintro ⟨w, rfl, hw⟩
      obtain ⟨w', rfl, hw'⟩ := ih.mp hw
      exact ⟨w', (M.isg_succ k w').symm, hw'⟩
    · rintro ⟨w, rfl, hw⟩
      exact ⟨M.isg k w, M.isg_succ k w, ih.mpr ⟨w, rfl, hw⟩⟩

/-- The preimage of a set under the `k`-fold singleton map. -/
def unsingN (k : ℕ) (a : V) : V := (M.unsing)^[k] a

theorem unsingN_succ (k : ℕ) (a : V) : M.unsingN (k + 1) a = M.unsing (M.unsingN k a) :=
  Function.iterate_succ_apply' _ _ _

theorem mem_unsingN {k : ℕ} {a p : V} : M.mem p (M.unsingN k a) ↔ M.mem (M.isg k p) a := by
  induction k generalizing p with
  | zero => exact Iff.rfl
  | succ k ih => rw [unsingN_succ, mem_unsing, ih, isg_succ']

/-- The membership relation raised `r` times: `{⟨ι^(r+1) x, ι^r y⟩ | x ∈ y}`. -/
def EN (r : ℕ) : V := (M.SI)^[r] M.E0

theorem EN_succ (r : ℕ) : M.EN (r + 1) = M.SI (M.EN r) :=
  Function.iterate_succ_apply' _ _ _

theorem mem_EN {r : ℕ} {p : V} : M.mem p (M.EN r) ↔
    ∃ x y, p = M.op (M.isg (r + 1) x) (M.isg r y) ∧ M.mem x y := by
  induction r generalizing p with
  | zero => exact M.mem_E0
  | succ r ih =>
    rw [EN_succ, mem_SI]
    constructor
    · rintro ⟨z, w, rfl, h⟩
      obtain ⟨x, y, h', hxy⟩ := ih.mp h
      obtain ⟨rfl, rfl⟩ := M.op_inj h'
      exact ⟨x, y, by rw [M.isg_succ (r + 1) x, M.isg_succ r y], hxy⟩
    · rintro ⟨x, y, rfl, hxy⟩
      exact ⟨M.isg (r + 1) x, M.isg r y, by rw [M.isg_succ (r + 1) x, M.isg_succ r y],
        ih.mpr ⟨x, y, rfl, hxy⟩⟩

/-! ## Codes of assignments -/

/-- The code of an assignment `env` to the variables of the context `Γ`. The context lists, for
each variable, the number of singletons needed to raise it to the level of the empty tuple; each
further variable in the tuple costs two more. -/
def code : List ℕ → List V → V
  | s :: Γ, a :: env => M.op (M.isg (s + 2 * Γ.length) a) (code Γ env)
  | _, _ => M.univ

theorem code_cons (s : ℕ) (Γ : List ℕ) (a : V) (env : List V) :
    M.code (s :: Γ) (a :: env) = M.op (M.isg (s + 2 * Γ.length) a) (M.code Γ env) := rfl

theorem isg_cons (s s' : ℕ) (Γ : List ℕ) (a : V) :
    M.isg (s + 2 * (s' :: Γ).length) a = M.sing (M.sing (M.isg (s + 2 * Γ.length) a)) := by
  have e : s + 2 * (s' :: Γ).length = s + 2 * Γ.length + 1 + 1 := by
    rw [List.length_cons]
    omega
  rw [e, isg_succ, isg_succ]

theorem code_inj {Γ : List ℕ} {env env' : List V} (h : env.length = Γ.length)
    (h' : env'.length = Γ.length) (hc : M.code Γ env = M.code Γ env') : env = env' := by
  induction Γ generalizing env env' with
  | nil => rw [List.length_eq_zero_iff.mp h, List.length_eq_zero_iff.mp h']
  | cons s Γ ih =>
    cases env with
    | nil => simp at h
    | cons a env =>
      cases env' with
      | nil => simp at h'
      | cons a' env' =>
        rw [code_cons, code_cons] at hc
        obtain ⟨h1, h2⟩ := M.op_inj hc
        rw [M.isg_inj h1, ih (by simpa using h) (by simpa using h') h2]

/-- The set of all codes of assignments to the context `Γ`. -/
def U : List ℕ → V
  | [] => M.sing M.univ
  | s :: Γ => M.prod (M.simgN (s + 2 * Γ.length) M.univ) (U Γ)

theorem mem_U {Γ : List ℕ} {c : V} :
    M.mem c (M.U Γ) ↔ ∃ env : List V, env.length = Γ.length ∧ c = M.code Γ env := by
  induction Γ generalizing c with
  | nil =>
    show M.mem c (M.sing M.univ) ↔ _
    rw [M.mem_sing]
    constructor
    · rintro rfl
      exact ⟨[], rfl, rfl⟩
    · rintro ⟨env, h, rfl⟩
      rw [List.length_eq_zero_iff.mp h]
      rfl
  | cons s Γ ih =>
    show M.mem c (M.prod (M.simgN (s + 2 * Γ.length) M.univ) (M.U Γ)) ↔ _
    rw [mem_prod]
    constructor
    · rintro ⟨q, r, rfl, hq, hr⟩
      obtain ⟨a, rfl, -⟩ := M.mem_simgN.mp hq
      obtain ⟨env, h, rfl⟩ := ih.mp hr
      exact ⟨a :: env, by simp [h], rfl⟩
    · rintro ⟨env, h, rfl⟩
      cases env with
      | nil => simp at h
      | cons a env =>
        exact ⟨_, _, rfl, M.mem_simgN.mpr ⟨a, rfl, M.mem_univ⟩,
          ih.mpr ⟨env, by simpa using h, rfl⟩⟩

/-- The `i`-th projection, as a relation between the raised `i`-th value and the code. -/
def P : List ℕ → ℕ → V
  | [], _ => M.emp
  | s :: Γ, 0 => M.int (M.I3 M.idr) (M.vx (M.U (s :: Γ)))
  | s :: Γ, i + 1 => M.int (M.I2 (P Γ i)) (M.vx (M.U (s :: Γ)))

theorem mem_P {Γ : List ℕ} {i : ℕ} {z : V} : M.mem z (M.P Γ i) ↔
    ∃ (env : List V) (a : V) (s : ℕ), env.length = Γ.length ∧ Γ[i]? = some s ∧
      env[i]? = some a ∧ z = M.op (M.isg (s + 2 * Γ.length) a) (M.code Γ env) := by
  induction Γ generalizing i z with
  | nil =>
    constructor
    · intro h
      exact absurd h M.not_mem_emp
    · rintro ⟨env, a, s, -, h, -⟩
      simp at h
  | cons s₀ Γ ih =>
    cases i with
    | zero =>
      show M.mem z (M.int (M.I3 M.idr) (M.vx (M.U (s₀ :: Γ)))) ↔ _
      rw [mem_int, mem_I3, mem_vx]
      constructor
      · rintro ⟨⟨a, b, c, rfl, hab⟩, q, r, h, hr⟩
        obtain ⟨-, rfl⟩ := M.op_inj h
        obtain ⟨a', h'⟩ := M.mem_idr.mp hab
        obtain ⟨rfl, rfl⟩ := M.op_inj h'
        obtain ⟨env, hlen, hc⟩ := M.mem_U.mp hr
        cases env with
        | nil => simp at hlen
        | cons a₀ env =>
          rw [code_cons] at hc
          obtain ⟨rfl, rfl⟩ := M.op_inj hc
          refine ⟨a₀ :: env, a₀, s₀, hlen, rfl, rfl, ?_⟩
          rw [isg_cons, code_cons]
      · rintro ⟨env, a, s, hlen, hs, ha, rfl⟩
        cases env with
        | nil => simp at hlen
        | cons a₀ env =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hs ha
          subst hs ha
          rw [isg_cons, code_cons]
          exact ⟨⟨_, _, _, rfl, M.mem_idr.mpr ⟨_, rfl⟩⟩, _, _, rfl,
            M.mem_U.mpr ⟨a₀ :: env, hlen, rfl⟩⟩
    | succ i =>
      show M.mem z (M.int (M.I2 (M.P Γ i)) (M.vx (M.U (s₀ :: Γ)))) ↔ _
      rw [mem_int, mem_I2, mem_vx]
      constructor
      · rintro ⟨⟨a, b, c, rfl, hac⟩, q, r, h, hr⟩
        obtain ⟨-, rfl⟩ := M.op_inj h
        obtain ⟨env, aᵢ, sᵢ, hlen, hs, ha, hz⟩ := ih.mp hac
        obtain ⟨rfl, rfl⟩ := M.op_inj hz
        obtain ⟨env', hlen', hc⟩ := M.mem_U.mp hr
        cases env' with
        | nil => simp at hlen'
        | cons a₀ env' =>
          rw [code_cons] at hc
          obtain ⟨rfl, hc'⟩ := M.op_inj hc
          have henv := M.code_inj hlen (by simpa using hlen') hc'
          subst henv
          refine ⟨a₀ :: env, aᵢ, sᵢ, by simp [hlen], by simpa using hs, by simpa using ha, ?_⟩
          rw [isg_cons, code_cons]
      · rintro ⟨env, a, s, hlen, hs, ha, rfl⟩
        cases env with
        | nil => simp at hlen
        | cons a₀ env =>
          have hlen' : env.length = Γ.length := by simpa using hlen
          rw [List.getElem?_cons_succ] at hs ha
          rw [isg_cons, code_cons]
          exact ⟨⟨_, _, _, rfl, ih.mpr ⟨env, a, s, hlen', hs, ha, rfl⟩⟩, _, _, rfl,
            M.mem_U.mpr ⟨a₀ :: env, hlen, rfl⟩⟩

end NFModel

/-! ## Formulas -/

/-- Formulas of the language of set theory, in de Bruijn form. Variable `0` is the most recently
bound one. Each quantifier carries a type for its variable. -/
inductive Fm : Type
  | mem (i j : ℕ) : Fm
  | eq (i j : ℕ) : Fm
  | neg (φ : Fm) : Fm
  | and (φ ψ : Fm) : Fm
  | all (t : ℕ) (φ : Fm) : Fm

/-- Satisfaction of a formula by a list of values in a structure `(V, mem)`. The types at the
quantifiers play no role. -/
def Sat {V : Type} (mem : V → V → Prop) : Fm → List V → Prop
  | .mem i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ mem a b
  | .eq i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ a = b
  | .neg φ, env => ¬Sat mem φ env
  | .and φ ψ, env => Sat mem φ env ∧ Sat mem ψ env
  | .all _ φ, env => ∀ a, Sat mem φ (a :: env)

/-- `Strat Γ φ`: the formula `φ` is stratified, where `Γ` lists the types of its free variables
and each bound variable has the type written at its quantifier. -/
def Strat : List ℕ → Fm → Prop
  | Γ, .mem i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some (t + 1)
  | Γ, .eq i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some t
  | Γ, .neg φ => Strat Γ φ
  | Γ, .and φ ψ => Strat Γ φ ∧ Strat Γ ψ
  | Γ, .all t φ => Strat (t :: Γ) φ

/-- Stratification with the types counted downwards: `x ∈ y` requires the number of `x` to be one
more than the number of `y`. This is the form used in the proof, where the number of a variable
is the number of singletons applied to it. -/
def CoStrat : List ℕ → Fm → Prop
  | Γ, .mem i j => ∃ s, Γ[i]? = some (s + 1) ∧ Γ[j]? = some s
  | Γ, .eq i j => ∃ s, Γ[i]? = some s ∧ Γ[j]? = some s
  | Γ, .neg φ => CoStrat Γ φ
  | Γ, .and φ ψ => CoStrat Γ φ ∧ CoStrat Γ ψ
  | Γ, .all s φ => CoStrat (s :: Γ) φ

/-- The largest type written at a quantifier. -/
def Fm.bound : Fm → ℕ
  | .mem _ _ => 0
  | .eq _ _ => 0
  | .neg φ => φ.bound
  | .and φ ψ => max φ.bound ψ.bound
  | .all t φ => max t φ.bound

/-- Replace each type `t` at a quantifier by `B - t`. -/
def Fm.flip (B : ℕ) : Fm → Fm
  | .mem i j => .mem i j
  | .eq i j => .eq i j
  | .neg φ => .neg (φ.flip B)
  | .and φ ψ => .and (φ.flip B) (ψ.flip B)
  | .all t φ => .all (B - t) (φ.flip B)

theorem sat_flip {V : Type} (mem : V → V → Prop) (B : ℕ) (φ : Fm) :
    ∀ env : List V, Sat mem (φ.flip B) env ↔ Sat mem φ env := by
  induction φ with
  | mem i j => exact fun _ => Iff.rfl
  | eq i j => exact fun _ => Iff.rfl
  | neg φ ih => exact fun env => not_congr (ih env)
  | and φ ψ ihφ ihψ => exact fun env => and_congr (ihφ env) (ihψ env)
  | all t φ ih => exact fun env => forall_congr' fun a => ih (a :: env)

theorem costrat_flip (B : ℕ) (φ : Fm) : ∀ Γ : List ℕ, Strat Γ φ → (∀ t ∈ Γ, t ≤ B) →
    φ.bound ≤ B → CoStrat (Γ.map (B - ·)) (φ.flip B) := by
  induction φ with
  | mem i j =>
    rintro Γ ⟨t, hi, hj⟩ hΓ -
    have ht : t + 1 ≤ B := hΓ _ (List.mem_of_getElem? hj)
    refine ⟨B - (t + 1), ?_, ?_⟩
    · rw [List.getElem?_map, hi, Option.map_some]
      congr 1
      omega
    · rw [List.getElem?_map, hj, Option.map_some]
  | eq i j =>
    rintro Γ ⟨t, hi, hj⟩ - -
    refine ⟨B - t, ?_, ?_⟩
    · rw [List.getElem?_map, hi, Option.map_some]
    · rw [List.getElem?_map, hj, Option.map_some]
  | neg φ ih => exact fun Γ h hΓ hb => ih Γ h hΓ hb
  | and φ ψ ihφ ihψ =>
    exact fun Γ h hΓ hb => ⟨ihφ Γ h.1 hΓ ((le_max_left _ _).trans hb),
      ihψ Γ h.2 hΓ ((le_max_right _ _).trans hb)⟩
  | all t φ ih =>
    intro Γ h hΓ hb
    have ht : t ≤ B := (le_max_left _ _).trans hb
    have := ih (t :: Γ) h (fun t' ht' => by
      rcases List.mem_cons.mp ht' with rfl | h'
      · exact ht
      · exact hΓ t' h') ((le_max_right _ _).trans hb)
    exact this

theorem exists_bound (L : List ℕ) : ∃ B, ∀ t ∈ L, t ≤ B := by
  induction L with
  | nil => exact ⟨0, fun t ht => by simp at ht⟩
  | cons a L ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨max a B, fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | h
    · exact le_max_left _ _
    · exact (hB t h).trans (le_max_right _ _)

namespace NFModel

variable {V : Type} (M : NFModel V)

/-! ## The induction on formulas -/

/-- For a stratified formula, the set of codes of the assignments that satisfy it exists. -/
theorem exists_codes (φ : Fm) : ∀ Γ : List ℕ, CoStrat Γ φ →
    ∃ S, ∀ c, M.mem c S ↔
      ∃ env : List V, env.length = Γ.length ∧ c = M.code Γ env ∧ Sat M.mem φ env := by
  induction φ with
  | mem i j =>
    rintro Γ ⟨s, hi, hj⟩
    refine ⟨M.rng (M.int (M.comp (M.conv (M.EN (s + 2 * Γ.length))) (M.P Γ i)) (M.P Γ j)),
      fun c => ?_⟩
    rw [mem_rng]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨hQ, hPj⟩ := M.mem_int.mp hz
      obtain ⟨b, a, c', hbc, hE, hPi⟩ := M.mem_comp.mp hQ
      obtain ⟨hzb, hcc⟩ := M.op_inj hbc
      subst hzb hcc
      obtain ⟨x, y, hxy, hmem⟩ := M.mem_EN.mp (M.mem_conv_op.mp hE)
      obtain ⟨hax, hzy⟩ := M.op_inj hxy
      obtain ⟨env, aᵢ, sᵢ, hlen, hsi, hai, hz1⟩ := M.mem_P.mp hPi
      obtain ⟨ha1, hc1⟩ := M.op_inj hz1
      obtain ⟨env', aⱼ, sⱼ, hlen', hsj, haj, hz2⟩ := M.mem_P.mp hPj
      obtain ⟨hz3, hc2⟩ := M.op_inj hz2
      have henv := M.code_inj hlen hlen' (hc1.symm.trans hc2)
      subst henv
      rw [hi] at hsi
      rw [hj] at hsj
      obtain rfl : s + 1 = sᵢ := Option.some.inj hsi
      obtain rfl : s = sⱼ := Option.some.inj hsj
      have e : s + 1 + 2 * Γ.length = s + 2 * Γ.length + 1 := by omega
      rw [e] at ha1
      have hx : x = aᵢ := M.isg_inj (hax.symm.trans ha1)
      have hy : y = aⱼ := M.isg_inj (hzy.symm.trans hz3)
      subst hx hy
      exact ⟨env, hlen, hc1, x, y, hai, haj, hmem⟩
    · rintro ⟨env, hlen, rfl, a, b, ha, hb, hab⟩
      have e : s + 1 + 2 * Γ.length = s + 2 * Γ.length + 1 := by omega
      refine ⟨M.isg (s + 2 * Γ.length) b, M.mem_int.mpr ⟨M.mem_comp.mpr
        ⟨_, M.isg (s + 2 * Γ.length + 1) a, _, rfl,
          M.mem_conv_op.mpr (M.mem_EN.mpr ⟨a, b, rfl, hab⟩), ?_⟩,
        M.mem_P.mpr ⟨env, b, s, hlen, hj, hb, rfl⟩⟩⟩
      refine M.mem_P.mpr ⟨env, a, s + 1, hlen, hi, ha, ?_⟩
      rw [e]
  | eq i j =>
    rintro Γ ⟨s, hi, hj⟩
    refine ⟨M.rng (M.int (M.P Γ i) (M.P Γ j)), fun c => ?_⟩
    rw [mem_rng]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨h1, h2⟩ := M.mem_int.mp hz
      obtain ⟨env, a, sᵢ, hlen, hsi, hai, hz1⟩ := M.mem_P.mp h1
      obtain ⟨env', b, sⱼ, hlen', hsj, hbj, hz2⟩ := M.mem_P.mp h2
      obtain ⟨hza, hc1⟩ := M.op_inj hz1
      obtain ⟨hzb, hc2⟩ := M.op_inj hz2
      have henv := M.code_inj hlen hlen' (hc1.symm.trans hc2)
      subst henv
      rw [hi] at hsi
      rw [hj] at hsj
      obtain rfl : s = sᵢ := Option.some.inj hsi
      obtain rfl : s = sⱼ := Option.some.inj hsj
      exact ⟨env, hlen, hc1, a, b, hai, hbj, M.isg_inj (hza.symm.trans hzb)⟩
    · rintro ⟨env, hlen, rfl, a, b, ha, hb, rfl⟩
      exact ⟨M.isg (s + 2 * Γ.length) a, M.mem_int.mpr
        ⟨M.mem_P.mpr ⟨env, a, s, hlen, hi, ha, rfl⟩, M.mem_P.mpr ⟨env, a, s, hlen, hj, hb, rfl⟩⟩⟩
  | neg φ ih =>
    intro Γ h
    obtain ⟨S, hS⟩ := ih Γ h
    refine ⟨M.diff (M.U Γ) S, fun c => ?_⟩
    rw [mem_diff, mem_U, hS]
    constructor
    · rintro ⟨⟨env, hlen, rfl⟩, hn⟩
      exact ⟨env, hlen, rfl, fun hs => hn ⟨env, hlen, rfl, hs⟩⟩
    · rintro ⟨env, hlen, rfl, hs⟩
      refine ⟨⟨env, hlen, rfl⟩, ?_⟩
      rintro ⟨env', hlen', hc, hs'⟩
      have henv := M.code_inj hlen hlen' hc
      subst henv
      exact hs hs'
  | and φ ψ ihφ ihψ =>
    intro Γ h
    obtain ⟨S₁, hS₁⟩ := ihφ Γ h.1
    obtain ⟨S₂, hS₂⟩ := ihψ Γ h.2
    refine ⟨M.int S₁ S₂, fun c => ?_⟩
    rw [mem_int, hS₁, hS₂]
    constructor
    · rintro ⟨⟨env, hlen, rfl, hs⟩, env', hlen', hc, hs'⟩
      have henv := M.code_inj hlen hlen' hc
      subst henv
      exact ⟨env, hlen, rfl, hs, hs'⟩
    · rintro ⟨env, hlen, rfl, hs, hs'⟩
      exact ⟨⟨env, hlen, rfl, hs⟩, env, hlen, rfl, hs'⟩
  | all s φ ih =>
    intro Γ h
    obtain ⟨S, hS⟩ := ih (s :: Γ) h
    refine ⟨M.diff (M.U Γ) (M.rng (M.diff (M.U (s :: Γ)) S)), fun c => ?_⟩
    rw [mem_diff, mem_U, mem_rng]
    constructor
    · rintro ⟨⟨env, hlen, rfl⟩, hn⟩
      refine ⟨env, hlen, rfl, fun a => ?_⟩
      by_contra hna
      apply hn
      have hlen1 : (a :: env).length = (s :: Γ).length := by simp [hlen]
      refine ⟨M.isg (s + 2 * Γ.length) a, M.mem_diff.mpr
        ⟨M.mem_U.mpr ⟨a :: env, hlen1, rfl⟩, ?_⟩⟩
      rw [hS]
      rintro ⟨env', hlen', hc, hs'⟩
      have henv := M.code_inj hlen1 hlen' hc
      subst henv
      exact hna hs'
    · rintro ⟨env, hlen, rfl, hall⟩
      refine ⟨⟨env, hlen, rfl⟩, ?_⟩
      rintro ⟨z, hz⟩
      obtain ⟨hU, hnS⟩ := M.mem_diff.mp hz
      obtain ⟨env', hlen', hc⟩ := M.mem_U.mp hU
      cases env' with
      | nil => simp at hlen'
      | cons a env' =>
        rw [code_cons] at hc
        obtain ⟨-, hc'⟩ := M.op_inj hc
        have henv := M.code_inj hlen (by simpa using hlen') hc'
        subst henv
        have hlen1 : (a :: env).length = (s :: Γ).length := by simp [hlen]
        exact hnS ((hS _).mpr ⟨a :: env, hlen1, by rw [code_cons, (M.op_inj hc).1], hall a⟩)

/-! ## Comprehension -/

/-- Comprehension for a formula stratified with the types counted downwards. -/
theorem comprehension_co {s : ℕ} {Γ : List ℕ} {φ : Fm} (h : CoStrat (s :: Γ) φ)
    (params : List V) (hp : params.length = Γ.length) :
    ∃ y, ∀ x, M.mem x y ↔ Sat M.mem φ (x :: params) := by
  obtain ⟨S, hS⟩ := M.exists_codes φ (s :: Γ) h
  refine ⟨M.unsingN (s + 2 * Γ.length)
    (M.dom (M.int S (M.vx (M.sing (M.code Γ params))))), fun x => ?_⟩
  rw [mem_unsingN, mem_dom]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hzS, hzv⟩ := M.mem_int.mp hz
    obtain ⟨q, r, hqr, hr⟩ := M.mem_vx.mp hzv
    obtain ⟨-, hzr⟩ := M.op_inj hqr
    have hzc : z = M.code Γ params := hzr.trans ((M.mem_sing _ _).mp hr)
    obtain ⟨env, hlen, hc, hs⟩ := (hS _).mp hzS
    cases env with
    | nil => simp at hlen
    | cons a env =>
      rw [code_cons] at hc
      obtain ⟨hx, hc'⟩ := M.op_inj hc
      have henv := M.code_inj hp (by simpa using hlen) (hzc.symm.trans hc')
      subst henv
      rw [M.isg_inj hx]
      exact hs
  · intro hs
    have hlen1 : (x :: params).length = (s :: Γ).length := by simp [hp]
    exact ⟨M.code Γ params, M.mem_int.mpr ⟨(hS _).mpr ⟨x :: params, hlen1, rfl, hs⟩,
      M.mem_vx.mpr ⟨_, _, rfl, (M.mem_sing _ _).mpr rfl⟩⟩⟩

/-- **Hailperin's theorem.** Every instance of stratified comprehension holds in a model of the
finitely many axioms: if `φ` is stratified, with the comprehension variable first and the
parameters after it, then `{x | φ(x, params)}` is a set. -/
theorem comprehension {t : ℕ} {Γ : List ℕ} {φ : Fm} (h : Strat (t :: Γ) φ)
    (params : List V) (hp : params.length = Γ.length) :
    ∃ y, ∀ x, M.mem x y ↔ Sat M.mem φ (x :: params) := by
  obtain ⟨B₀, hB₀⟩ := exists_bound (t :: Γ)
  have hΓ : ∀ t' ∈ t :: Γ, t' ≤ max B₀ φ.bound := fun t' ht' =>
    (hB₀ t' ht').trans (le_max_left _ _)
  have hco := costrat_flip (max B₀ φ.bound) φ (t :: Γ) h hΓ (le_max_right _ _)
  obtain ⟨y, hy⟩ := M.comprehension_co (s := max B₀ φ.bound - t)
    (Γ := Γ.map (max B₀ φ.bound - ·)) (φ := φ.flip (max B₀ φ.bound)) hco params
    (by simpa using hp)
  exact ⟨y, fun x => (hy x).trans (sat_flip M.mem _ φ _)⟩

end NFModel

/-! ## The statement -/

/-- NF: extensionality and the scheme of stratified comprehension. -/
structure IsNF (V : Type) (mem : V → V → Prop) : Prop where
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  comprehension : ∀ (t : ℕ) (Γ : List ℕ) (φ : Fm), Strat (t :: Γ) φ →
    ∀ params : List V, params.length = Γ.length → ∃ y, ∀ x, mem x y ↔ Sat mem φ (x :: params)

theorem NFModel.isNF {V : Type} (M : NFModel V) : IsNF V M.mem :=
  ⟨M.ext, fun _ _ _ h params hp => M.comprehension h params hp⟩

/-! ## Checks on the statement -/

/-- The universal set, by comprehension for `x = x`. -/
theorem IsNF.exists_univ {V : Type} {mem : V → V → Prop} (h : IsNF V mem) :
    ∃ y, ∀ x, mem x y := by
  obtain ⟨y, hy⟩ := h.comprehension 0 [] (.eq 0 0) ⟨0, rfl, rfl⟩ [] rfl
  exact ⟨y, fun x => (hy x).mpr ⟨x, x, rfl, rfl, rfl⟩⟩

/-- An instance with a parameter and a quantifier: `{x | ∃ z, z ∈ x ∧ z ∈ p}`, with `z` of type
`0` and `x`, `p` of type `1`. -/
theorem IsNF.exists_meets {V : Type} {mem : V → V → Prop} (h : IsNF V mem) (p : V) :
    ∃ y, ∀ x, mem x y ↔ ∃ z, mem z x ∧ mem z p := by
  obtain ⟨y, hy⟩ := h.comprehension 1 [1]
    (.neg (.all 0 (.neg (.and (.mem 0 1) (.mem 0 2))))) ⟨⟨0, rfl, rfl⟩, ⟨0, rfl, rfl⟩⟩ [p] rfl
  refine ⟨y, fun x => (hy x).trans ?_⟩
  simp [Sat]

/-- Russell's formula `x ∉ x` is not stratified, whatever type `x` is given. -/
theorem not_strat_russell (t : ℕ) : ¬Strat [t] (.neg (.mem 0 0)) := by
  rintro ⟨s, h1, h2⟩
  simp at h1 h2
  omega

end ConNF.NF

#print axioms ConNF.NF.NFModel.comprehension
