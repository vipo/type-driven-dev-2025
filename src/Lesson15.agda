module Lesson15 where

open import Agda.Builtin.Bool

module Basics where
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

    if_then_else_ : {A : Set} → Bool → A → A → A
    if false then a else b = b
    if true then a else b = a

    f : Bool → ℕ
    f b = if b then 1 else 0

    data _×_ ( A B : Set) : Set where
        _,_ : A → B → A × B

    p : ℕ × Bool
    p = zero , true
    
module StackMachine where
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
    open import Data.List using (List; []; [_]; _∷_; _++_)
    open import Data.Maybe
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import Data.List.Properties using (++-assoc)

    data Binop : Set where
        Plus : Binop
        Times : Binop

    data Exp : Set where
        Const : ℕ → Exp
        Op : Binop → Exp → Exp → Exp

    binopEval : Binop → ℕ → ℕ → ℕ
    binopEval Plus v₁ v₂ = v₁ + v₂
    binopEval Times v₁ v₂ = v₁ * v₂

    expEval : Exp → ℕ
    expEval (Const x) = x
    expEval (Op x e₁ e₂) = (binopEval x) (expEval e₁) (expEval e₂)

    someExpr : Exp
    someExpr = Op Times (Op Plus (Const 2) (Const 3)) (Const 7)

    testEval : (expEval someExpr) ≡ 35
    testEval = refl

    data Instr : Set where
        IConst : ℕ → Instr
        IOp : Binop → Instr

    Prog = List Instr
    Stack = List ℕ

    evalInst : Instr → Stack → Maybe Stack
    evalInst (IConst x) s = just (x ∷ s)
    evalInst (IOp x) (x₁ ∷ x₂ ∷ s) = just ((binopEval x x₁ x₂) ∷ s)
    evalInst (IOp x) _ = nothing

    evalProg : Prog → Stack → Maybe Stack
    evalProg [] s = just s
    evalProg (x ∷ p) s with evalInst x s
    ...                | nothing = nothing
    ...                | just y = evalProg p y

    compile : Exp → Prog
    compile (Const x) = [ IConst x ]
    compile (Op x e₁ e₂) = compile e₂ ++ compile e₁ ++ [ IOp x ]

    compileCorrect : ∀ (e : Exp) → ∀ (p : Prog) → ∀ (s : Stack) →
                     evalProg (compile e ++ p) s ≡ evalProg p (expEval e ∷ s)
    compileCorrect (Const x) p s = refl
    compileCorrect (Op x e₁ e₂) p s rewrite 
          ++-assoc (compile e₂) (compile e₁ ++ [ IOp x ]) p
        | ++-assoc (compile e₁) [ IOp x ] p
        | compileCorrect e₂ (compile e₁ ++ IOp x ∷ p) s
        | compileCorrect e₁ (IOp x ∷ p) (expEval e₂ ∷ s)
        = refl
