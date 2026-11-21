import NumericalEmitterBatch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
open NF192.Emitter NF192.Emitter.Registers NF192.Numerical
namespace SevenEmitter

def sw (r : Register) : Register := if r=1 then 8 else if r=8 then 1 else r
private theorem involutive : ∀ r : Register, sw (sw r)=r := by decide

def exchange (s : Registers) : Registers := fun r => s (sw r)

def change : Code → Code
  | .inc n => .inc (sw n)
  | .dec n => .dec (sw n)
  | .br n => .br n
  | .cont n => .cont n
  | .halt => .halt
  | .seq a b => .seq (change a) (change b)

@[simp] private theorem exch_get (s : Registers) (r : Register) : exchange s (sw r)=s r := by
  simp [exchange,involutive]

@[simp] private theorem exch_set (s : Registers) (r : Register) (v : Nat) :
    exchange (s.set r v) = (exchange s).set (sw r) v := by
  funext i
  by_cases h : i=sw r
  · subst i; simp [exchange,involutive]
  · have nh : sw i≠r := fun e => h ((involutive i).symm.trans (congrArg sw e))
    simp [exchange,Registers.set,h,nh]

@[simp] private theorem exch_add (s : Registers) (r : Register) (v : Nat) :
    exchange (s.add r v) = (exchange s).add (sw r) v := by
  simp [Registers.add]

theorem change_eval {c : Code} {s t : Registers} {f : Flow} (e : Eval c s f t) :
    Eval (change c) (exchange s) f (exchange t) := by
  induction e with
  | inc r s => simpa only [change,exch_add] using Eval.inc (sw r) (exchange s)
  | dec_pos r s h =>
    simpa only [change,exch_set,exch_get] using Eval.dec_pos (sw r) (exchange s) (by simpa using h)
  | dec_zero r s h => exact Eval.dec_zero _ _ (by simpa using h)
  | br => exact Eval.br _ _
  | cont => exact Eval.cont _ _
  | halt => exact Eval.halt _
  | seq_normal _ _ h k => exact Eval.seq_normal h k
  | seq_br_left _ h => exact Eval.seq_br_left h
  | seq_br_left_more _ h => exact Eval.seq_br_left_more h
  | seq_cont_left _ h => exact Eval.seq_cont_left h
  | seq_halt_left _ h => exact Eval.seq_halt_left h
  | seq_br_right _ _ h k => exact Eval.seq_br_right h k
  | seq_cont_right_more _ _ h k => exact Eval.seq_cont_right_more h k
  | seq_halt_right _ _ h k => exact Eval.seq_halt_right h k
  | seq_loop _ _ _ h k l => exact Eval.seq_loop h k l

@[simp] private theorem exch_mk9 (n t st c a b v w p : Nat) :
    exchange (mk9 n t st c a b v w p)=mk9 n p st c a b v w t := by
  funext i
  fin_cases i <;> rfl

def split := change Literal.seq115

theorem split_pair (n st c a b x y p : Nat) :
    Eval split (mk9 n (pair x y) st c a b 0 0 p) .normal (mk9 n 0 st c a b x y p) := by
  simpa only [split,exch_mk9,pair_zero_zero,Nat.zero_add,Cantor.unpair_pair] using change_eval (seq115_eval n p st c a b 0 0 (pair x y))

def project (right : Bool) : Code :=
  .seq (.seq Literal.seq121 split)
    (if right then .seq (clearCode 6) (transferCode 7 1) else .seq (clearCode 7) (transferCode 6 1))

theorem project_pair (side : Bool) (n t st c a x y p : Nat) :
    Eval (project side) (mk9 n t st c a (pair x y) 0 0 p) .normal
      (mk9 n (if side then y else x) (pair t st) c a (pair x y) 0 0 p) := by
  have push := seq121_normal n t st c a (pair x y) p
  have start := Eval.seq_normal push (split_pair n (pair t st) c a (pair x y) x y p)
  cases side with
  | false =>
    apply Eval.seq_normal start
    apply Eval.seq_normal (t:=mk9 n 0 (pair t st) c a (pair x y) x 0 p)
    · simpa using clear_eval 7 (mk9 n 0 (pair t st) c a (pair x y) x y p)
    · simpa [Registers.add] using transfer_eval 6 1 (by decide) (mk9 n 0 (pair t st) c a (pair x y) x 0 p)
  | true =>
    apply Eval.seq_normal start
    apply Eval.seq_normal (t:=mk9 n 0 (pair t st) c a (pair x y) 0 y p)
    · simpa using clear_eval 6 (mk9 n 0 (pair t st) c a (pair x y) x y p)
    · simpa [Registers.add] using transfer_eval 7 1 (by decide) (mk9 n 0 (pair t st) c a (pair x y) 0 y p)

#print axioms project_pair

inductive Token where
  | leftB | rightB | a | c | pair1 | implic

def effect (t : Token) (f : Frame) : Frame :=
  match t with
  | .leftB => f.push (Cantor.unpair f.b).1
  | .rightB => f.push (Cantor.unpair f.b).2
  | .a => f.apply .push4
  | .c => f.apply .push3
  | .pair1 => f.apply .eqn
  | .implic => f.apply .imp

def code : Token → Code
  | .leftB => project false
  | .rightB => project true
  | .a => Macro.block .push4
  | .c => Macro.block .push3
  | .pair1 => Macro.block .eqn
  | .implic => Macro.block .imp

theorem atom_eval (t : Token) (f : Frame) : Eval (code t) f.regs .normal (effect t f).regs := by
  obtain ⟨n,top,st,c,a,b,p⟩ := f
  obtain ⟨x,y,hb⟩ : ∃ x y, b=pair x y :=
    ⟨_,_,(Cantor.pair_unpair b).symm⟩
  subst b
  cases t with
  | leftB => simpa [code,effect,Frame.regs,Frame.push,Cantor.unpair_pair] using
      project_pair false n top st c a x y p
  | rightB => simpa [code,effect,Frame.regs,Frame.push,Cantor.unpair_pair] using
      project_pair true n top st c a x y p
  | a => exact macro_eval .push4 _
  | c => exact macro_eval .push3 _
  | pair1 => exact macro_eval .eqn _
  | implic => exact macro_eval .imp _

inductive Body where
  | atom (t : Token) | seq (a b : Body)

def compile : Body → Code
  | .atom t => code t
  | .seq a b => .seq (compile a) (compile b)

def applyBody : Body → Frame → Frame
  | .atom t, f => effect t f
  | .seq a b, f => applyBody b (applyBody a f)

theorem body_eval (b : Body) (f : Frame) :
    Eval (compile b) f.regs .normal (applyBody b f).regs := by
  induction b generalizing f with
  | atom t => exact atom_eval t f
  | seq _ _ ha hb => exact Eval.seq_normal (ha f) (hb _)

def body : Body := (.seq (.seq (.seq (.atom .leftB) (.seq (.atom .rightB) (.atom .pair1))) (.seq (.seq (.atom .a) (.atom .c)) (.seq (.atom .pair1) (.atom .leftB)))) (.seq (.seq (.seq (.atom .a) (.atom .pair1)) (.seq (.atom .rightB) (.atom .c))) (.seq (.seq (.atom .pair1) (.atom .pair1)) (.seq (.atom .implic) (.atom .implic)))))

def formula (f g x y : Nat) := imp (eqn f g) (imp (eqn x y) (eqn (app f x) (app g y)))

theorem emits (n top st c a f g p : Nat) :
    Eval (compile body) (mk9 n top st c a (pair f g) 0 0 p) .normal
      (mk9 n (formula f g a c) (pair top st) c a (pair f g) 0 0 p) := by
  have h := body_eval body ⟨n,top,st,c,a,pair f g,p⟩
  simpa only [body,applyBody,effect,Frame.apply,Frame.push,Frame.combine,Frame.regs,
    Cantor.unpair_pair,formula,ctor,imp,eqn,app,Nat.add_zero] using h

#print axioms emits
end SevenEmitter
