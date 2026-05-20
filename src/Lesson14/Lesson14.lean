
inductive Binop where
  | Plus : Binop
  | Times : Binop

inductive Exp where
  | Const : Nat → Exp
  | Op : Binop → Exp → Exp → Exp

def binopEval : Binop → Nat → Nat → Nat
  | Binop.Plus,  k, j => k + j
  | Binop.Times, k, j => k * j

def expEval : Exp → Nat
  | Exp.Const k => k
  | Exp.Op binop y z => binopEval binop (expEval y) (expEval z)

inductive Instr where
  | IConst : Nat → Instr
  | IOp : Binop → Instr

abbrev Prog := List Instr
abbrev Stack := List Nat

def evalInst : Instr → Stack → Option Stack
  | Instr.IConst k, ks           => some (k :: ks)
  | Instr.IOp x,    y :: z :: xs => some (binopEval x y z :: xs)
  | Instr.IOp _,    _            => none

def evalProg : Prog → Stack → Option Stack
  | [],      ks => some ks
  | x :: xs, ks => match evalInst x ks with
    | none   => none
    | some y => evalProg xs y

def compile : Exp → Prog
  | Exp.Const k    => [.IConst k]
  | Exp.Op x e1 e2 => compile e2 ++ compile e1 ++ [.IOp x]

#check List.append_assoc

theorem compileCorrect (e : Exp) (p : Prog) (s : Stack) :
    evalProg (compile e ++ p) s = evalProg p (expEval e :: s) := by
    induction e generalizing p s with
       | Const k => simp [evalProg, evalInst, compile, expEval]
       | Op x e1 e2 ih1 ih2 =>
          simp only [compile, expEval]
          rw [List.append_assoc, List.append_assoc]
          rw [ih2, ih1]
          simp [evalProg, evalInst]
