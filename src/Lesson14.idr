module Lesson14

import Data.List
import Data.Nat

%default total

data Binop = Plus | Times

data Exp : Type where
    Const : Nat -> Exp
    Op : Binop -> Exp -> Exp -> Exp

binopEval : Binop -> Nat -> Nat -> Nat
binopEval Plus k j = k + j
binopEval Times k j = k * j

expEval : Exp -> Nat
expEval (Const k) = k
expEval (Op binop x y) = (binopEval binop) (expEval x) (expEval y)

someExpr : Exp
someExpr = Op Times (Op Plus (Const 2) (Const 3)) (Const 7)

testEval : (expEval Lesson14.someExpr) = 35
testEval = Refl

data Instr : Type where
    IConst : Nat -> Instr
    IOp : Binop -> Instr

Prog = List Instr
Stack = List Nat

evalInst : Instr -> Stack -> Maybe Stack
evalInst (IConst k) ks = Just (k :: ks)
evalInst (IOp x) (y :: z :: xs) = Just (binopEval x y z :: xs)
evalInst (IOp x) _ = Nothing

evalProg : Prog -> Stack -> Maybe Stack
evalProg [] ks = Just ks
evalProg (x :: xs) ks = case evalInst x ks of
                             Nothing => Nothing
                             (Just y) => evalProg xs y

compile : Exp -> Prog
compile (Const k) = [IConst k]
compile (Op x e1 e2) = (compile e2) ++ (compile e1) ++ [IOp x]

testCompile : compile Lesson14.someExpr = [IConst 7, IConst 3, IConst 2, IOp Plus, IOp Times]
testCompile = Refl

testRun : evalProg (compile Lesson14.someExpr) [] = Just [35]
testRun = Refl

appendAssociativeRev : (l, c, r : List a) -> (l ++ c) ++ r = l ++ (c ++ r)
appendAssociativeRev l c r = rewrite sym (appendAssociative l c r) in Refl

compileCorrect : (e : Exp) -> (p : Prog) -> (s : Stack) ->
                 evalProg (compile e ++ p) s = evalProg p (expEval e :: s)
compileCorrect (Const k) p s = Refl
compileCorrect (Op x e1 e2) p s =
    rewrite appendAssociativeRev (compile e2) (compile e1 ++ [IOp x]) p in
    rewrite appendAssociativeRev (compile e1) [IOp x] p in
    rewrite compileCorrect e2 (compile e1 ++ (IOp x :: p)) s in
    rewrite compileCorrect e1 (IOp x :: p) (expEval e2 :: s) in
    Refl
