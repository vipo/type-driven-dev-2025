module Lesson13.Main
import Data.Vect
import Lesson13.Undestroyable

-- Erasure

f1 : Vect n a
f1 = ?f1_rhs

f2 : {n : _} -> {a : _} -> Vect n a
f2 = ?f2_rhs

f2' : {0 n : _} -> {a : _} -> Vect n a
f2' = ?f2'_rhs

f2'' : {0 n : _} -> {a : _} -> Vect n a
f2'' {n} = f1 {n=n}

failing
    f2''' : {0 n : _} -> {a : _} -> Vect n a
    f2''' {n = 0} = ?f2'''_rhs_0
    f2''' {n = (S k)} = ?f2'''_rhs_1

data Some : Type -> Type where
    MkSome : (0 x : Nat) -> Some a

MkSomeT : (0 n : Nat) -> Some a
MkSomeT x = MkSome x

failing
    MkSomeT' : (0 n : Nat) -> Some a
    MkSomeT' 0 = ?asdasd_0
    MkSomeT' (S k) = ?asdasd_1

0 MkSomeT'' : (0 n : Nat) -> Some a
MkSomeT'' 0 = ?asdasd_0
MkSomeT'' (S k) = ?asdasd_1

-- Linear (Q=1)

drop' : a -> ()
drop' x = ()

dupl' : a -> (a, a)
dupl' x = (x, x)

failing
    drop : (1 _ : a) -> ()
    drop _ = ()

failing
    dupl : (1 _ : a) -> (a, a)
    dupl x = (x, x)


data Drill = MkDrill

failing
    destroyDrill : (1 _ : Drill) -> ()
    destroyDrill drill = ()

destroyDrill : (1 _ : Drill) -> ()
destroyDrill MkDrill = ()

-- export, public export


failing
    destroyUndT : (1 _ : UndT) -> ()
    destroyUndT _ = ()

failing
    destroyUndT : (1 _ : UndT) -> ()
    destroyUndT UndV = ()

destroyUndT : (1 _ : UndT) -> ()
destroyUndT u = dropUnd u

destroyUndT' : (1 _ : UndT) -> UndT
destroyUndT' x = x

-- context : ()
-- context =
--     let 1 u = mkUnd in
--     let 1 x = ?asddestroyUndT u in
--     ()

undProto : ()
undProto = mkUndF $ \u => dropUnd u

-- bad
undProto' : UndT
undProto' = mkUndF $ \u => u

undProtoIO : IO ()
undProtoIO = mkUndIO $ \u => let () = dropUnd u in pure ()

