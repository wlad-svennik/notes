import NF181PAPacked
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA192.Literal PA192.Numerals.FoundationRoute SetTheory.BusyBeaver.ZFC
open PA192.ModelSearch
namespace JointPool
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
open NF182PA.Pool (nativeB test)

def joint (f g x y : V) := imp (eqn f g) (imp (eqn x y) (eqn (app f x) (app g y)))

noncomputable def batch (a b c u : V) : List V :=
  [row0 a b c u,row3 a b,row6 a b c,nativeB a b c,
    joint (left b) (right b) a c,test b a,row8 a b]

def axiomJoint (p : V) : Prop := ∃ a b c u : V, ¬a<u ∧ p ∈ batch a b c u

instance axiomJointDef : Language.DefinablePred ℒₒᵣ (axiomJoint (V:=V)) := by
  unfold axiomJoint batch
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  unfold row0 row3 nativeB row6 joint test NF182PA.Pool.single row8
  definability

theorem ax_of_mem {a b c u p : V} (hu : ¬a<u) (hp : p∈batch a b c u) :
    axiomJoint p := ⟨a,b,c,u,hu,hp⟩

theorem restrictedJoint {P : V → Prop} (ax : ∀ p, axiomJoint p → P p)
    (mp : ∀ {a b}, P (imp a b) → P a → P b) : DominatedImplication.Restricted domin P where
  mp := mp
  rho8 := fun _ _ _ _ hu => ax _ (ax_of_mem (not_lt_of_ge hu) (.head _))

def Line (ctx pool k p : V) : Prop :=
  axiomJoint p ∨ p∈ctx ∨ ∃ a j l, j<k ∧ l<k ∧ ⟪j,imp a p⟫∈pool ∧ ⟪l,a⟫∈pool

def Valid (ctx pool : V) : Prop := ∀ k p, ⟪k,p⟫∈pool → Line ctx pool k p
def Pr (ctx p : V) : Prop := ∃ pool k, Valid ctx pool ∧ ⟪k,p⟫∈pool

instance lineDef : Language.DefinableRel₄ ℒₒᵣ (Line (V:=V)) := by unfold Line; definability
instance validDef : Language.DefinableRel ℒₒᵣ (Valid (V:=V)) := by unfold Valid; definability
instance provDef : Language.DefinableRel ℒₒᵣ (Pr (V:=V)) := by unfold Pr; definability

theorem line_mono {s t p q k a : V} (st : s⊆t) (pq : p⊆q)
    (h : Line s p k a) : Line t q k a := by
  rcases h with ax | hh | ⟨b,j,l,hj,hl,hm,ha⟩
  · exact Or.inl ax
  · exact Or.inr (Or.inl (st hh))
  · exact Or.inr (Or.inr ⟨b,j,l,hj,hl,pq hm,pq ha⟩)

theorem mono {s t a : V} (st : s⊆t) (h : Pr s a) : Pr t a := by
  obtain ⟨pool,k,hp,hk⟩ := h
  exact ⟨pool,k,fun j f hf => line_mono st (fun _ hx => hx) (hp j f hf),hk⟩

theorem leaf {s a : V} (h : axiomJoint a ∨ a∈s) : Pr s a := by
  refine ⟨{⟪0,a⟫},0,?_,by simp⟩
  intro j p hp
  have he : j=0 ∧ p=a := by simpa using hp
  rw [he.2]
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem mp {s a b : V} (hmaj : Pr s (imp a b)) (hmin : Pr s a) : Pr s b := by
  obtain ⟨pool,j,hp,hj⟩ := hmaj
  obtain ⟨other,l,ho,hl⟩ := hmin
  let r := max j l+1
  let united : V := insert ⟪r,b⟫ (pool ∪ other)
  have ps : pool⊆united := by intro x hx; simp [united,hx]
  have os : other⊆united := by intro x hx; simp [united,hx]
  refine ⟨united,r,?_,by simp [united]⟩
  intro k p h
  rcases mem_bitInsert_iff.mp h with e | old
  · obtain ⟨rfl,rfl⟩ := pair_ext_iff.mp e
    exact Or.inr (Or.inr ⟨a,j,l,lt_succ_iff_le.mpr (le_max_left j l),
      lt_succ_iff_le.mpr (le_max_right j l),ps hj,os hl⟩)
  · rcases mem_cup_iff.mp old with h₁ | h₂
    · exact line_mono (fun _ hx => hx) ps (hp k p h₁)
    · exact line_mono (fun _ hx => hx) os (ho k p h₂)

theorem restrictedPr (s : V) : DominatedImplication.Restricted domin (Pr s) :=
  restrictedJoint (fun _ h => leaf (Or.inl h)) mp

theorem weaken {s a : V} (q : V) (ha : Pr s a) : Pr s (imp q a) :=
  mp (DominatedImplication.k (restrictedPr s) a q) ha

theorem refl (s a : V) : Pr s (imp a a) :=
  mp (mp (DominatedImplication.s (restrictedPr s) a (imp a a) a)
       (DominatedImplication.k (restrictedPr s) a (imp a a))) (DominatedImplication.k (restrictedPr s) a a)

theorem deduction {s a b : V} (h : Pr (insert a s) b) : Pr s (imp a b) := by
  obtain ⟨pool,k,hp,hk⟩ := h
  have trans : ∀ n : V, ∀ j<n, ∀ p, ⟪j,p⟫∈pool → Pr s (imp a p) := by
    apply induction_of_arith
    · apply arithPred_of_definable
      definability
    · intro j hj
      change j<0 at hj
      exact False.elim ((not_lt_of_ge (show (0:V)≤j from zero_le)) hj)
    · intro n ih j hj p elem
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with jl | rfl
      · exact ih _ jl _ elem
      · rcases hp j p elem with ax | hh | ⟨c,k,l,hk,hl,h1,h2⟩
        · exact weaken _ (leaf (Or.inl ax))
        · rcases mem_bitInsert_iff.mp hh with rfl | hh
          · exact refl _ _
          · exact weaken _ (leaf (Or.inr hh))
        · exact mp (mp (DominatedImplication.s (restrictedPr s) a c p) (ih k hk _ h1))
            (ih l hl _ h2)
  exact trans (k+1) k (by simp) b hk

/-- The conclusion of every internally coded finite proof satisfies any
definable predicate closed under its local rules. This can connect the ranked
format directly to a tree-proof checker or a coded successful command word. -/
theorem realize {s b : V} {R : V → Prop} [Language.DefinablePred ℒₒᵣ R]
    (ha : ∀ p, axiomJoint p → R p) (hh : ∀ p, p∈s → R p)
    (hmp : ∀ a p, R (imp a p) → R a → R p) (h : Pr s b) : R b := by
  obtain ⟨pool,k,hp,hk⟩ := h
  have trans : ∀ n : V, ∀ j<n, ∀ p, ⟪j,p⟫∈pool → R p := by
    apply induction_of_arith
    · apply arithPred_of_definable
      definability
    · intro j hj
      change j<0 at hj
      exact False.elim ((not_lt_of_ge (show (0:V)≤j from zero_le)) hj)
    · intro n ih j hj p elem
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with jl | rfl
      · exact ih _ jl _ elem
      · rcases hp j p elem with ax | hyp | ⟨a,k,l,hk,hl,h1,h2⟩
        · exact ha _ ax
        · exact hh _ hyp
        · exact hmp _ _ (ih k hk _ h1) (ih l hl _ h2)
  exact trans (k+1) k (by simp) b hk



private theorem ax {ctx a b c p : V} (h : p∈batch a b c 0) : Pr ctx p :=
  leaf (Or.inl (ax_of_mem (not_lt_of_ge zero_le) h))

private theorem eu {ctx x y z : V} (xy : Pr ctx (eqn x y)) (xz : Pr ctx (eqn x z)) :
    Pr ctx (eqn z y) :=
  mp (mp (ax (a:=x) (b:=y) (c:=z) (p:=row6 x y z) (by simp [batch])) xy) xz

private theorem ident (ctx x : V) : Pr ctx (eqn x x) := by
  have h : Pr ctx (eqn (app (konst x) q) x) := ax (a:=q) (b:=x) (c:=0) (p:=row3 q x) (by simp [batch])
  exact eu h h

private theorem flip {ctx x y : V} (h : Pr ctx (eqn x y)) : Pr ctx (eqn y x) :=
  eu (ident ctx x) h

private theorem trans {ctx x y z : V} (h : Pr ctx (eqn x y)) (k : Pr ctx (eqn y z)) :
    Pr ctx (eqn x z) := eu k (flip h)

private theorem gen (ctx f g x y : V) : Pr ctx (joint f g x y) := by
  apply ax (a:=x) (b:=cantor f g) (c:=y)
  simp [batch]

theorem arg (ctx a b c : V) : Pr ctx (row2 a b c) := by
  apply deduction
  exact mp (mp (gen _ a a c b) (ident _ a)) (leaf (Or.inr (by simp)))

theorem funArg (ctx a b c : V) : Pr ctx (row4 a b c) := by
  apply deduction
  exact flip (mp (mp (gen _ a c b b) (leaf (Or.inr (by simp)))) (ident _ b))

theorem containsOld {ctx p : V} (h : NF182PA.Pool.axiom182 p) : Pr ctx p := by
  obtain ⟨a,b,c,u,hu,h⟩ := h
  simp only [NF182PA.Pool.batch,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h|h|h <;> subst p
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.head _)))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.head _))))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.head _)))))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.tail _ (.head _))))))
  · exact arg ctx a b c
  · exact funArg ctx a b c
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))

end JointPool

namespace OriginalJointProof
open NF182PA.Pool (Pr leaf mp batch ax_of_mem deduction)
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem ax {ctx a b c p : V} (h : p∈batch a b c 0) : Pr ctx p :=
  leaf (Or.inl (ax_of_mem (not_lt_of_ge zero_le) h))

private theorem eu {ctx x y z : V} (xy : Pr ctx (eqn x y)) (xz : Pr ctx (eqn x z)) :
    Pr ctx (eqn z y) :=
  mp (mp (ax (a:=x) (b:=y) (c:=z) (p:=row6 x y z) (by simp [batch])) xy) xz

private theorem ident (ctx x : V) : Pr ctx (eqn x x) := by
  have h : Pr ctx (eqn (app (konst x) q) x) := ax (a:=q) (b:=x) (c:=0) (p:=row3 q x) (by simp [batch])
  exact eu h h

private theorem flip {ctx x y : V} (h : Pr ctx (eqn x y)) : Pr ctx (eqn y x) :=
  eu (ident ctx x) h

private theorem trans {ctx x y z : V} (h : Pr ctx (eqn x y)) (k : Pr ctx (eqn y z)) :
    Pr ctx (eqn x z) := eu k (flip h)

theorem gen (ctx f g x y : V) : Pr ctx (JointPool.joint f g x y) := by
  apply deduction
  apply deduction
  have eqfg : Pr (insert (eqn x y) (insert (eqn f g) ctx)) (eqn f g) := leaf (Or.inr (by simp))
  have eqxy : Pr (insert (eqn x y) (insert (eqn f g) ctx)) (eqn x y) := leaf (Or.inr (by simp))
  have hf := flip (mp (ax (a:=f) (b:=x) (c:=g) (p:=row4 f x g) (by simp [batch])) eqfg)
  have hx := mp (ax (a:=g) (b:=y) (c:=x) (p:=row2 g y x) (by simp [batch])) eqxy
  exact trans hf hx

theorem containsJoint {ctx p : V} (h : JointPool.axiomJoint p) : Pr ctx p := by
  obtain ⟨a,b,c,u,hu,h⟩ := h
  simp only [JointPool.batch,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h|h <;> subst p
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.head _)))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.head _))))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.head _)))))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.tail _ (.head _))))))
  · exact gen ctx (left b) (right b) a c
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
  · exact leaf (Or.inl (ax_of_mem (a:=a) (b:=b) (c:=c) (u:=u) hu (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))

end OriginalJointProof

namespace JointPool
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem iff_original (ctx p : V) : Pr ctx p ↔ NF182PA.Pool.Pr ctx p := by
  letI : Language.DefinablePred ℒₒᵣ (NF182PA.Pool.Pr ctx) := by definability
  letI : Language.DefinablePred ℒₒᵣ (Pr ctx) := by definability
  constructor
  · apply realize
    · intro x hx; exact OriginalJointProof.containsJoint hx
    · intro x hx; exact NF182PA.Pool.leaf (Or.inr hx)
    · intro a x major minor; exact NF182PA.Pool.mp major minor
  · apply NF182PA.Pool.realize
    · intro x hx; exact containsOld hx
    · intro x hx; exact leaf (Or.inr hx)
    · intro a x major minor; exact mp major minor
#print axioms iff_original
end JointPool
