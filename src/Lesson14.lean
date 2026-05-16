inductive Binop where
  | Plus : Binop
  | Times : Binop

inductive Exp where
  | Const : Nat → Exp
  | Op : Binop → Exp → Exp → Exp
