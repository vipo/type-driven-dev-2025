module Lesson03

import Data.Vect

%default total

index' : Fin k -> Vect k a -> a
index' FZ (x :: xs) = x
index' (FS x) (y :: xs) = index' x xs

-- format "%s = %d" : String -> Int -> String
-- format "Hello" : String
-- format "Hello, %s" : String -> String
-- format "%d %d" : Int -> Int -> String


data Format = Number Format |
              Str Format |
              Lit Char Format |
              End

-- %s = %d -> Format
-- Str (Lit ' ' (Lit '=' (Lit ' ' (Number End))))

FormatType : Format -> Type
FormatType (Number x) = Int -> FormatType x
FormatType (Str x) = String -> FormatType x
FormatType (Lit _ x) = FormatType x
FormatType End = String

toFormat : List Char -> Format
toFormat [] = End
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat (x :: xs) = Lit x (toFormat xs)

format : (fmt : Format) -> String -> FormatType fmt
format (Number x) acc = \i => format x (acc ++ show i)
format (Str x) acc = \str => format x (acc ++ str)
format (Lit c x) acc = format x (acc ++ (pack [c]))
format End str = str

Eq Format where
    (Number x) == (Number y) = x == y
    (Str x) == (Str y) = x == y
    (Lit c x) == (Lit d y) = x == y && c == d
    End == End = True
    a == b = False

interface FuzzyEq a where
    (~==~) : a -> a -> Bool

FuzzyEq Int where
    (~==~) a b = a - b <= 1
