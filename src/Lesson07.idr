module Lesson07
import Data.List
import Data.Nat
import Data.Fin
import Data.So
import Decidable.Equality

%default total


namespace TypesAreStatements

    namespace Implication

        apply : (a -> b) -> a -> b
        apply f x = f x

        trans : (a -> b) -> (b -> c) -> a -> c
        trans f g x = g (f x)


        {-
        A => B,  A
        ----------- (MP, =>Elim)
            B

            a => b,  b => c
            -----------------  (transitivity)
                a => c

        a, b, c -- atomic propositions.

        -}

        {-
        A => B,  B
        ----------- (!!! invalid)
            A

        -}
        ylppa : (a -> b) -> b -> a
        ylppa f x = ?ylppa_rhs


        magic' : Type -> Nat
        magic' x = 0

        magic : a
        magic = ?magic_rhs

        magic_nat : Nat
        magic_nat = 0

        ylppa_ns : (String -> Nat) -> Nat -> String
        ylppa_ns f x = "hey"


    namespace Conjunction

        {-
        A /\ B
        ---------- (/\-Elim-1)
            A

        A /\ B
        ---------- (/\-Elim-2)
            B

        A, B
        ---------- (/\-Intro)
        A /\ B
        -}

        fst : (a, b) -> a
        fst (x, y) = x

        snd : (a, b) -> b
        snd (x, y) = y

        pair : a -> b -> (a, b)
        pair x y = (x, y)

    namespace BoolValues

        tt : ()
        tt = ()
        
        ff : Void

    namespace Disjunction

        {-
            A
        ---------- (\/-Intro-1)
        A \/ B

            B
        ---------- (\/-Intro-1)
        A \/ B


        A => Q, B => Q, A \/ B
        -------------------------- (\/-Elim, proof by cases)
                Q

        -}

        opt_a : a -> Either a b
        opt_a x = Left x

        opt_b : b -> Either a b
        opt_b x = Right x

        disj_elim : (a -> q) -> (b -> q) -> Either a b -> q
        disj_elim f g (Left x) = f x
        disj_elim f g (Right x) = g x

    namespace Negation

        {-
            ~A
        -}

        -- neg : a -> Void
        -- neg x = ?neg_rhs

        -- A => B    ====>    ~B => ~A
        contra_pos : (a -> b) -> (Not b -> Not a)
        contra_pos f a n = a (f n)

namespace ImplIsProof

        -- Typing relation: env ⊢ a : t
        -- For a function apply:
        --
        --   env ⊢ f : t -> u,  env ⊢ a : t
        --  ----------------------------------- (fn-appl)
        --          env ⊢ f a : u
        --
        -- Keep only the types:
        --     T => U, T
        --   ------------ (MP)
        --         U

        --    env ⊢ e : (t, u)
        --  -------------------- (for a pair, also types are `/\ elim_1`)
        --    env ⊢ fst e : t

        --    env ⊢ e : (t, u)
        --  -------------------- (for a pair, also types are `/\ elim_2`)
        --    env ⊢ snd e : u

        apply : (a -> b) -> a -> b
        apply f x = f x

namespace EvalIsSimpl

    -- B => A => (A /\ B)  (note the reversed order)

    {- =================== Proof as in math books ==================
    |  THEOREM: B ⇒ A ⇒ (A ∧ B).
    |
    |  LEMMA 1: (B ∧ A) ⇒ (A ∧ B).
    |  Proof.
    |  Suffices assume (B ∧ A) and prove (A ∧ B) by "⇒-intro".
    |  From (B ∧ A) we have (A) by "∧-elim2".
    |  From (B ∧ A) we have (B) by "∧-elim1".
    |  From (A) and (B) we have (A ∧ B) by "∧-intro". □
    |
    |  Proof of the THEOREM.
    |  Suffices assume (B) and prove (A ⇒ A ∧ B) by "⇒-intro".
    |  Next, suffices assume (A) and prove (A ∧ B) by "⇒-intro".
    |  From (B) and (A) we have (B ∧ A) by "∧-intro".
    |  From (B ∧ A) we have (A, B) by "LEMMA 1". □
    -}

    {- ============================== Formal: LEMMA 1 ==============================
    |  ------------------------------ (ax)          ------------------------------ (ax)
    |   (B ∧ A) ⊢ (B ∧ A), (A ∧ B)                (B ∧ A) ⊢ (B ∧ A), (A ∧ B)
    |  ------------------------------ (∧-elim)     ------------------------------- (∧-elim)
    |       (B ∧ A) ⊢ A, (A ∧ B)                       (B ∧ A) ⊢ B, (A ∧ B)
    |      --------------------------------------------------------------------- (∧-intro)
    |                          (B ∧ A) ⊢ (A ∧ B), (A ∧ B)
    |                         ------------------------------ (contr)
    |                               (B ∧ A) ⊢ (A ∧ B)
    |                            ------------------------ (⇒-intro)
    |                              ⊢ (B ∧ A) ⇒ (A ∧ B)
    |-}

    {- ============================== Formal: THEOREM ==============================
    |                                       ----------- (ax)   ----------- (ax)
    |                                        B, A ⊢ B           B, A ⊢ A
    |    ---------------------- (LEMMA 1)   ------------------------------ (∧-intro)
    |     ⊢ (B ∧ A) ⇒ (A ∧ B)                     B, A  ⊢ (B ∧ A)
    |    ------------------------------------------------------------ (⇒-elim, MP)
    |                          B, A  ⊢ (A ∧ B)
    |                         ------------------ (⇒-intro)
    |                          B ⊢ A ⇒ (A ∧ B)
    |                        -------------------- (⇒-intro)
    |                         ⊢ B ⇒ A ⇒ (A ∧ B)
    |-}

    ||| We will have 2 proofs of the same type.
    -- B => A => (A /\ B)  (note the reversed order)
    pair_t : {a: Type} -> {b : Type} -> Type
    pair_t = (b -> a -> (a, b))

    ||| The initial proof.
    pair_2 : pair_t {a} {b}
    pair_2 y x = (\z => ((snd z), (fst z))) (y, x) -- note, inverted

    pair_3 : pair_t {a} {b}
    pair_3 y x = ((snd (y, x)), (fst (y, x)))

    pair_4 : pair_t {a} {b}
    pair_4 y x = (x, y)

    --  B => A => (A /\ B) -- had before.
    -- (B /\ A) => (A /\ B) --.
    pair_4' : (b, a) -> (a, b)
    pair_4' (y, x) = (x, y)

    {- ========================= THEOREM (simplified) =========================
    |    ------------ (ax)     ----------- (ax)
    |      B, A ⊢ A             B, A ⊢ B
    |    ---------------------------------- (∧-intro)
    |             B, A ⊢ (A ∧ B)
    |          ------------------- (⇒-intro)
    |            B ⊢ A ⇒ (A ∧ B)
    |         ---------------------- (⇒-intro)
    |           ⊢ B ⇒ A ⇒ (A ∧ B)
    |-}

    {- =================== Proof as in math books ==================
    |  THEOREM: B ⇒ A ⇒ (A ∧ B).
    |
    |  Proof of the THEOREM.
    |  Suffices assume (B) and prove (A ⇒ A ∧ B) by "⇒-intro".
    |  Next, suffices assume (A) and prove (A ∧ B) by "⇒-intro".
    |  We have both (A) and (B), thus (A ∧ B) by "∧-intro". □
    -}

    add_num : Nat -> Nat -> Nat
    add_num k j = k + j
    
    add_num' : Nat -> Nat -> Nat
    add_num' k j = 0

    {- ================ Curry-Howard Isomorphism ================
    |            Types <-> Theorems
    |         Programs <-> Proofs
    |       Evaluation <-> Simplification
    | Note: (data structures are functions thus programs)
    |-}
