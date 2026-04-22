module Lesson10
import Data.Bits
import Data.Stream
import Data.Primitives.Views
import System
%default total

namespace Label

    export
    labelFrom : Integer -> List a -> List (Integer, a)
    labelFrom i [] = []
    labelFrom i (x :: xs) = (i, x) :: (labelFrom (i+1) xs)

    export
    label : List a -> List (Integer, a)
    label = labelFrom 0

    failing
        countFrom : Integer -> List Integer
        countFrom n = n :: (countFrom (n+1))

    public export
    data InfList : Type -> Type where
        (::) : (value : e) -> Inf (InfList e) -> InfList e

    export
    countFrom : Integer -> InfList Integer
    countFrom i = i :: (countFrom (i+1))

    export
    getPrefix : (count : Nat) -> InfList a -> List a
    getPrefix 0 x = []
    getPrefix (S k) (value :: x) = value :: (getPrefix k (x))

    {-
        Functions are total if they:
          - cover all the cases
          - deconstructing a value and processing recursively its argument (which is smaller).
          - a function is productive.
    -}

    {-
        Recursion - consumes data
        CoRecursion - produces data.
    -}

namespace S

    export
    labelWith : Stream l -> List a -> List (l, a)
    labelWith s [] = []
    labelWith (y :: z) (x :: xs) = (y, x) :: labelWith z xs

    export
    label : List a -> List (Integer, a)
    label l = labelWith (iterate (+1) 0) l


namespace F

    public export
    data InfIO : Type where
        Do : IO a -> (a -> Inf InfIO) -> InfIO

    export
    loopPrint : String -> InfIO
    loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)

    export
    covering -- Non-terminating for now.
    run' : InfIO -> IO ()
    run' (Do action cont) = do res <- action
                               run' (cont res)


    public export
    data Fuel = Dry | More Fuel

    export
    tank : Nat -> Fuel
    tank 0 = Dry
    tank (S k) = More (tank k)

    export -- Now it's total
    run : Fuel -> InfIO -> IO ()
    run Dry y = putStrLn "Out of fuel..."
    run (More f) (Do act cnt) = do res <- act
                                   run f (cnt res)

namespace F2

    public export
    data Fuel' = Dry | More (Lazy Fuel')

    export
    covering -- This cannot be total.
    forever : Fuel'
    forever = More forever

    export
    tank : Nat -> Fuel'
    tank 0 = Dry
    tank (S k) = More (tank k)

    export -- Now it's total
    run : Fuel' -> InfIO -> IO ()
    run Dry y = putStrLn "Out of fuel..."
    run (More f) (Do act cnt) = do res <- act
                                   run f (cnt res)

    covering
    main : IO ()
    main = run (forever) (F.loopPrint "a")
