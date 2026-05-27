Require Import Bool Arith List.
Import ListNotations.
Require Extraction.
Set Implicit Arguments.


Check 5.
Check tt.
Check unit.
Check true.
Check True.

Compute 3.

Lemma example1: forall a b: Prop, a /\ b -> b /\ a.
intros a b H.
split.
destruct H as [H1 H2].
exact H2.
destruct H as [H1 H2].
exact H1.
Qed.


Inductive binop : Set := Plus | Times.

Check binop_rec.
Check binop_rect.
Check binop_ind.
Check binop_sind.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopEval (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expEval (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b op1 op2 => (binopEval b) (expEval op1) (expEval op2)
  end.

Eval simpl in expEval (Binop Times (Const 2) (Const 2)).
Compute expEval (Binop Times (Const 2) (Const 2)).

Inductive instr : Set :=
|iConst : nat -> instr
|iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.


Definition evalInstr (i : instr) (s: stack) : option stack :=
  match i with
  |iConst n => Some (n :: s)
  |iBinop b =>
    match s with
    | arg1 :: arg2 :: s' =>
      Some ((binopEval b) arg1 arg2 :: s')
    | _ => None
    end
  end.

Fixpoint evalProg (p : prog) (s : stack) : option stack :=
  match p with
  | [] => Some (s)
  | i :: p' =>
    match evalInstr i s with
    |None => None
    |Some s' => evalProg p' s'
    end
  end.

Fixpoint compile (e : exp) : prog :=
  match e with
  |Const n => iConst n :: []
  |Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: []
  end.

Compute evalProg (compile(Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7))) [].

Check app_assoc.

Lemma app_assoc_rev:
  forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ (m ++ n).
Proof.
  symmetry.
  rewrite app_assoc.
  reflexivity.
Qed.

Theorem compile_correct :
  forall e p s, evalProg (compile e ++ p) s = evalProg p (expEval e :: s).
Proof.
induction e.
intros.
simpl.
reflexivity.
intros.
simpl.
rewrite app_assoc_rev.
rewrite app_assoc_rev.
rewrite IHe2.
rewrite IHe1.
simpl.
reflexivity.
Qed.

Print compile_correct.

Extraction Language OCaml.
Extraction compile.