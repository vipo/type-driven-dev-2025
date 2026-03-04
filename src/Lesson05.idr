module Lesson05

import Data.Vect

%default total

v : Vect 3 Int
v = [1,2,3]


readVector : (len: Nat) -> IO (Vect len String)
readVector 0 = pure []
readVector (S k) =
    do x <- getLine
       xs <- readVector k
       pure (x :: xs)

failing
    readVector' : IO (Vect len String)
    readVector' =
        do x <- getLine
           xs <- readVector'
           pure (x :: xs)

data VectUnknown : Type -> Type where
    MkVect : (len : Nat) -> Vect len a -> VectUnknown a

Show a => Show (VectUnknown a) where
    show (MkVect len xs) = show xs

covering
readVectUnknown : IO (VectUnknown String)
readVectUnknown =
    do x <- getLine
       if x == ""
          then pure (MkVect 0 [])
          else do MkVect k xs <- readVectUnknown
                  pure (MkVect (S k) (x :: xs))

anyV : (len ** Vect len String)
anyV = (1 ** ["f"])

covering
readVectUnknown' : IO (len ** Vect len String)
readVectUnknown' =
    do x <- getLine
       if x == ""
          then pure (0 ** [])
          else do (k ** xs) <- readVectUnknown'
                  pure (S k ** x :: xs)

covering
readVectUnknown'' : IO (len ** Vect len String)
readVectUnknown'' =
    do x <- getLine
       if x == ""
          then pure (_ ** [])
          else do (_ ** xs) <- readVectUnknown'
                  pure (_ ** x :: xs)
failing
    exactLen : {len2 : Nat} -> (len1: Nat) -> Vect len2 a -> Maybe (Vect len1 a)
    exactLen {len2} len1 xs = case len2 == len1 of
                                False => Nothing
                                True => Just xs

data EqNat : (nat1 : Nat) -> (nat2 : Nat) -> Type where
    Same : (nat : Nat) -> EqNat nat nat

t1 : EqNat 1 1
t1 = Same 1

t2 : EqNat 2 1
t2 = ?fdf

sameS : (k: Nat) -> (j:Nat) -> EqNat k j -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)

sameS' : EqNat k j -> EqNat (S k) (S j)
sameS' (Same j) = Same (S j)

checkEqNat : (nat1 : Nat) -> (nat2 : Nat) -> Maybe(EqNat nat1 nat2)
checkEqNat 0 0 = Just (Same 0)
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just x) => Just (sameS' x)

exactLen' : {len2 : Nat} -> (len1: Nat) -> Vect len2 a -> Maybe (Vect len1 a)
exactLen' {len2} len1 xs = case checkEqNat len1 len2 of
                            Nothing => Nothing
                            (Just (Same len2)) => Just xs

covering
zipInput : IO ()
zipInput = do (len1 ** vec1) <- readVectUnknown'
              (len2 ** vec2) <- readVectUnknown'
              case exactLen' len1 vec2 of
                   Nothing => putStrLn "Vector lengths are different"
                   (Just x) => putStrLn (show (zip vec1 x))

rt : 1 = 1
rt = Refl

rt' : 2 = 1
rt' = ?rt'_rhs

checkEqNat' : (nat1 : Nat) -> (nat2 : Nat) -> Maybe(nat1 = nat2)
checkEqNat' 0 0 = Just Refl
checkEqNat' 0 (S k) = Nothing
checkEqNat' (S k) 0 = Nothing
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                               Nothing => Nothing
                               (Just Refl) => Just Refl

exactLen'' : {len2 : Nat} -> (len1: Nat) -> Vect len2 a -> Maybe (Vect len1 a)
exactLen'' {len2} len1 xs = case checkEqNat' len1 len2 of
                                    Nothing => Nothing
                                    (Just Refl) => Just xs

covering
zipInput' : IO ()
zipInput' = do (len1 ** vec1) <- readVectUnknown'
               (len2 ** vec2) <- readVectUnknown'
               case exactLen'' len1 vec2 of
                   Nothing => putStrLn "Vector lengths are different"
                   (Just x) => putStrLn (show (zip vec1 x))
