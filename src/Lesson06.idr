module Lesson06

import Data.Vect
import Decidable.Equality

%default total

rt : 1 = 1
rt = Refl

rt' : 1 = 2

t' : Void -> Int
t' _ = 42

t1 : Void -> 3 = 3
t1 x = Refl

t2 : Void -> 3 = 2
t2 x impossible

t3 : 2 = 3 -> Void
t3 Refl impossible

failing 
    t4 : 2 = 2 -> Void
    t4 Refl impossible

zeroNotSucc : 0 = S k -> Void
zeroNotSucc Refl impossible

succNotZero : S k = 0 -> Void
succNotZero Refl impossible

noRec : (k = j -> Void) -> Not (S k = S j)
noRec f Refl = f Refl

checkEqNat : (nat1 : Nat) -> (nat2 : Nat) -> Dec(nat1 = nat2)
checkEqNat 0 0 = Yes Refl
checkEqNat 0 (S k) = No zeroNotSucc
checkEqNat (S k) 0 = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              (Yes prf) => Yes (cong S prf)
                              (No contra) => No (noRec contra)

exactLen : {len2 : Nat} -> (len1: Nat) -> Vect len2 a -> Maybe (Vect len1 a)
exactLen {len2} len1 xs = case checkEqNat len1 len2 of
                               (Yes Refl) => Just xs
                               (No contra) => Nothing

exactLen' : {len2 : Nat} -> (len1: Nat) -> Vect len2 a -> Maybe (Vect len1 a)
exactLen' len1 xs = case decEq len1 len2 of
                         (Yes Refl) => Just xs
                         (No contra) => Nothing


--- more sophisticated

--Can't solve constraint between: plus len 1 and S len.

test0 : plus 1 b = S b
test0 = Refl

test1 : plus b 1 = S b
test1 = ?test1_rhs

plus1NComm : (a : Nat) -> 1 + a = a + 1
plus1NComm a = plusCommutative 1 a

-- 1 + a = plus 1 a = S (plus 0 a) = S a

fixMath : Vect (plus len 1) a -> Vect (plus 1 len) a
fixMath xs = rewrite plus1NComm len in xs

myReverse : Vect n a -> Vect n a
myReverse [] = []
myReverse (x :: xs) = fixMath (myReverse xs ++ [x])
