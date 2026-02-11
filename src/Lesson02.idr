module Lesson02

import Data.List
import Data.Vect

%default total

-- ADT
-- Enumeration

data Direction = North | East | South | West

turn : Direction -> Direction
turn North = East
turn East = South
turn South = West
turn West = North

-- Union
data Shape = Triangle Double Double
           | Rectangle Double Double

data Picture = Primitive Shape
             | Combine Shape Shape

testPicture : Picture
testPicture = Combine (Triangle 1 1) (Triangle 0 0)

-- Generics
data Tree a = Empty | Node (Tree a) (Tree a) a
%name Tree tree, tree1, tree2

insert : Ord e => e -> Tree e -> Tree e
insert x Empty = Node Empty Empty x
insert x orig@(Node tree tree1 y) = case compare x y of
                                LT => Node (insert x tree) tree1 y
                                EQ => orig
                                GT => Node tree (insert x tree1) y

data BTree : Type -> Type where
    BEmpty : Ord a => BTree a
    BNode : Ord a => BTree a -> BTree a -> a -> BTree a

insert' : e -> BTree e -> BTree e
insert' x BEmpty = BNode BEmpty BEmpty x
insert' x (BNode y z w) = ?insert'_rhs_1

-- Dependant

n : Nat
n = 4

n' : Nat
n' = S(S(Z))

minusOne : Nat -> Nat
minusOne 0 = 0
minusOne (S k) = k

minusOneNat : Int -> Int
minusOneNat i = ?minusOneNat_rhs


data PowerSource = Petrol | Pedal

data Vehicle : PowerSource -> Type where
    Bicycle : Vehicle Pedal
    Tricycle : Vehicle Pedal
    Car : (fuel: Nat) -> Vehicle Petrol
    Bus : (fuel : Int) -> Vehicle Petrol

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car (S fuel)
refuel (Bus fuel) = Bus (fuel + 100)
refuel Bicycle impossible


-- Lists

l : List Int
l = 1 :: 2 :: Nil

l' : List Nat
l' = [1,2,3,4]

len : List a -> Nat
len [] = 0
len (_ :: xs) = S (len xs)

-- Vectors
ev : Vect 0 Int
ev = []

failing
    ev' : Vect 1 Int
    ev' = []

sev : Vect 1 Char
sev = ['a']

failing
    len' : Vect k a -> Nat
    len' xs = k

len'' : (k: Nat) -> Vect k a -> Nat
len'' k _ = k

len''' : {k: Nat} -> Vect k a -> Nat
len''' {k} _ = k
