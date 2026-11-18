module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Option
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Part
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SymmDiff
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Tactic

/-!
# The finite axiomatisation of NF (new file)

`NFModel V` is a structure on `V` that satisfies extensionality and finitely many existence axioms
in the style of Hailperin. This file contains the definition and two checks on it. It imports only
Mathlib. It was split off from `ConNF.NF.Model`, which constructs such a structure from the model
of tangled type theory, so that Hailperin's theorem (`ConNF.NF.Hailperin`) and everything that
uses it can be built without that construction.

The imports are the Mathlib modules that `ConNF.NF.Model` imports directly or through the files
of the con-nf project, so that the files which used to import `ConNF.NF.Model` see the same part
of Mathlib as before.
-/

@[expose] public section

namespace ConNF.NF

/-! ## The definition -/

/-- The data of a model of NF: a membership relation, with singleton and unordered pair
operations. -/
structure NFData (V : Type) where
  mem : V → V → Prop
  sing : V → V
  up : V → V → V

/-- The Kuratowski pair `{{x}, {x, y}}`. -/
def NFData.op {V : Type} (M : NFData V) (x y : V) : V := M.up (M.sing x) (M.up x y)

/-- A model of NF, in the finite axiomatisation used by the con-nf project: extensionality and the
type-erased forms of the Hailperin-style axioms of `ConNF.TTTModel`. -/
structure NFModel (V : Type) extends NFData V where
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  mem_sing : ∀ x y, mem y (sing x) ↔ y = x
  mem_up : ∀ x y z, mem z (up x y) ↔ z = x ∨ z = y
  inter : ∀ x y, ∃ w, ∀ z, mem z w ↔ mem z x ∧ mem z y
  compl : ∀ x, ∃ w, ∀ z, mem z w ↔ ¬mem z x
  singletonImage : ∀ x, ∃ y, ∀ z w,
    mem (toNFData.op (sing z) (sing w)) y ↔ mem (toNFData.op z w) x
  insertion2 : ∀ x, ∃ y, ∀ p q r,
    mem (toNFData.op (sing (sing p)) (toNFData.op q r)) y ↔ mem (toNFData.op p r) x
  insertion3 : ∀ x, ∃ y, ∀ p q r,
    mem (toNFData.op (sing (sing p)) (toNFData.op q r)) y ↔ mem (toNFData.op p q) x
  vCross : ∀ x, ∃ y, ∀ p, mem p y ↔ ∃ q r, p = toNFData.op q r ∧ mem r x
  typeLower : ∀ x, ∃ y, ∀ p, mem p y ↔ ∀ q, mem (toNFData.op q (sing p)) x
  converse : ∀ x, ∃ y, ∀ p q, mem (toNFData.op p q) y ↔ mem (toNFData.op q p) x
  cardinalOne : ∃ y, ∀ p, mem p y ↔ ∃ q, p = sing q
  subset : ∃ y, ∀ p q, mem (toNFData.op p q) y ↔ ∀ r, mem r p → mem r q

/-! ## Checks on the definition -/

/-- A model of these axioms has a universal set, and the universal set is a member of itself.
So the axioms are not satisfied by any well-founded structure. -/
theorem NFModel.exists_univ {V : Type} (M : NFModel V) :
    ∃ v, (∀ z, M.mem z v) ∧ M.mem v v := by
  obtain ⟨c, -⟩ := M.cardinalOne
  obtain ⟨n, hn⟩ := M.compl c
  obtain ⟨e, he⟩ := M.inter c n
  obtain ⟨v, hv⟩ := M.compl e
  have huniv : ∀ z, M.mem z v := fun z => (hv z).mpr fun hz =>
    (hn z).mp ((he z).mp hz).2 ((he z).mp hz).1
  exact ⟨v, huniv, huniv v⟩

/-- Hailperin's axiom P9 in its original form: the membership relation `{⟨{x}, y⟩ | x ∈ y}` is a
set. It follows from the inclusion axiom. -/
theorem NFModel.exists_memRel {V : Type} (M : NFModel V) :
    ∃ v, ∀ x y, M.mem (M.op (M.sing x) y) v ↔ M.mem x y := by
  obtain ⟨s, hs⟩ := M.subset
  refine ⟨s, fun x y => (hs (M.sing x) y).trans
    ⟨fun h => h x ((M.mem_sing x x).mpr rfl), fun h r hr => ?_⟩⟩
  rw [(M.mem_sing x r).mp hr]
  exact h

end ConNF.NF
