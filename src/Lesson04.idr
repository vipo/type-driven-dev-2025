module Lesson04

import Data.Vect
import System.REPL

%default total

-- adder 0 -> Int -> Int
-- adder 1 -> Int -> Int -> Int
-- adder 2 -> Int -> Int -> Int -> Int

AdderType : (num: Nat) -> Type
AdderType 0 = Int
AdderType (S k) = Int -> AdderType k

adder : (num : Nat) -> (acc : Int) -> AdderType num
adder 0 acc = acc
adder (S k) acc = \val => adder k (acc + val)

record StringDataStore where
    constructor MkStringDataStore
    size : Nat
    items : Vect size String

-- data StringDataStore = MkStringDataStore (size : Nat) -> (items : Vect size String)

one : StringDataStore
one = MkStringDataStore 1 ["fsdfd"]

two : StringDataStore
two = {items := ["1", "2"], size := 2} one

two' : StringDataStore
two' = {size $= plus 1, items $= ("0" ::) } one

addStringToTail : (items : Vect size String) -> (str : String) -> Vect (S size) String
addStringToTail [] str = [str]
addStringToTail (x :: xs) str = x :: addStringToTail xs str

addToStringDataStore : StringDataStore -> String -> StringDataStore
addToStringDataStore (MkStringDataStore size items) str =
    MkStringDataStore (S size) (addStringToTail items str)

infixr 5 .+.

data Schema = SInt | SString | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SInt = Int
SchemaType SString = String
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
    constructor MkDataStore
    schema : Schema
    size : Nat
    items : Vect size (SchemaType schema)

addToTail : Vect s t -> t -> Vect (S s) t
addToTail [] x = [x]
addToTail (y :: xs) x = y :: addToTail xs x

addToStore : (ds : DataStore) -> (SchemaType ds.schema) -> DataStore
addToStore ds x = {size := S ds.size, items := addToTail ds.items x} ds

empty : DataStore
empty = MkDataStore (SInt .+. SString) _ []

empty' : DataStore
empty' = MkDataStore (SInt) _ []

main : IO ()
main = do name <- getLine
          putStrLn ("Hello, " ++ name)

readNumber : IO (Maybe Nat)
readNumber =
    do input <- getLine
       if all isDigit (unpack input)
          then pure (Just (cast input))
          else pure Nothing

readTwoNumbers : IO (Maybe (Nat, Nat))
readTwoNumbers =
    do Just n1 <- readNumber | Nothing => pure Nothing
       Just n2 <- readNumber | Nothing => pure Nothing
       pure (Just (n1, n2))
