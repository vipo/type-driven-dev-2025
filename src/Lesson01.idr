module Lesson01

import Data.List
import Data.Vect

%default total

-- No general recursion
failing
    gr : Int
    gr = gr

i : Int
i = 424234234324 * 54545454353454

ii : Integer
ii = 424234234324 * 54545454353454

d : Double
d = 4234.443

b : Bool
b = False

s : String
s = "labas"

c : Char
c = 'a'

t : (Int, Integer, Char)
t = ?t_rhs

thrd : (a, b, c) -> c
thrd (x, (y, z)) = z

f : Bool -> String
f False = "false"
f True = "true"

StringOrInt : Bool -> Type
StringOrInt False = Int
StringOrInt True = String

stringOrInt : (x : Bool) -> StringOrInt x
stringOrInt False = 42
stringOrInt True = "Fourty two"

stringOrInt' : (x : Bool) -> StringOrInt x
stringOrInt' x =
    case x of
        False => 21
        True => "21"
