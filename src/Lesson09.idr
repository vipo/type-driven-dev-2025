module Lesson09

import Data.List
import Data.List.Views

%default total


namespace Last
  
  data ListLast : List a -> Type where
    Empty : ListLast []
    NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

  public export
  listLast : (xs : List a) -> ListLast xs
  listLast [] = Empty
  listLast (x :: xs) = case listLast xs of
                            Empty => NonEmpty [] x
                            (NonEmpty ys y) => NonEmpty (x :: ys) y

  describeLastHelper : Show a => (input : List a) -> ListLast input -> String
  describeLastHelper [] Empty = "Empty"
  describeLastHelper (xs ++ [x]) (NonEmpty xs x) = "Last element: " ++ show x

  public export
  describeLast : Show a => List a -> String
  describeLast xs = describeLastHelper xs (listLast xs)

  describeLast' : Show a => List a -> String
  describeLast' xs with (listLast xs)
    describeLast' [] | Empty = ?describeLast'_rhs_rhss_0
    describeLast' (ys ++ [x]) | (NonEmpty ys x) = ?describeLast'_rhs_rhss_1

  covering
  reverse' : List a -> List a
  reverse' xs with (listLast xs)
    reverse' [] | Empty = []
    reverse' (ys ++ [x]) | (NonEmpty ys x) = x :: (reverse' ys)

namespace Merge
  data SplitList : List a -> Type where
    SplitNil : SplitList []
    SplitOne : (x : a) -> SplitList [x]
    SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

  public export
  splitList : (input : List a) -> SplitList input
  splitList xs = splitListHelp xs xs
    where
      splitListHelp : List a -> (xs : List a) -> SplitList xs
      splitListHelp _ [] = SplitNil
      splitListHelp _ [x] = SplitOne x
      splitListHelp (_ :: _ :: counter) (x :: xs) =
        case splitListHelp counter xs of
          SplitNil => SplitOne x
          (SplitOne y) => SplitPair [x] [y]
          (SplitPair ls rs) => SplitPair (x :: ls) rs
      splitListHelp _ xs = SplitPair [] xs

  covering
  public export
  mergeSort : Ord a => List a -> List a
  mergeSort xs with (splitList xs)
    mergeSort [] | SplitNil = []
    mergeSort [x] | (SplitOne x) = [x]
    mergeSort (lefts ++ rights) | (SplitPair lefts rights) =
      merge (mergeSort lefts) (mergeSort rights)

namespace Rec
  data SnocList' : List a -> Type where
    Empty : SnocList' []
    Snoc : (xs : List a) -> (x : a) -> (rec : SnocList' xs) -> SnocList' (xs ++ [x])

  snocListHelper :
        {xs : List a} -> (snoc : SnocList' xs) ->
        (rest : List a) -> SnocList' (xs ++ rest)
  snocListHelper snoc [] =
        rewrite appendNilRightNeutral xs in snoc
  snocListHelper {xs} snoc (x :: ys) =
        rewrite appendAssociative xs [x] ys in
        snocListHelper (Snoc xs x snoc) ys

  snocList' : (xs : List a) -> SnocList' xs
  snocList' xs = snocListHelper Empty xs

  reverseHelper : (input : List a) -> SnocList' input -> List a
  reverseHelper [] Empty = []
  reverseHelper (xs ++ [x]) (Snoc xs x rec) = x :: reverseHelper xs rec

  reverse' : List a -> List a
  reverse' xs = reverseHelper xs (snocList' xs)

  reverse'': List a -> List a
  reverse'' xs with (snocList' xs)
    reverse'' [] | Empty = []
    reverse'' (ys ++ [x]) | (Snoc ys x rec) = x :: reverse'' ys | rec

namespace Vanilla
  mergeSort' : Ord a => List a -> List a
  mergeSort' xs with (splitRec xs)
    mergeSort' [] | SplitRecNil = []
    mergeSort' [x] | (SplitRecOne x) = [x]
    mergeSort' (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec) =
      merge (mergeSort' lefts | lrec) (mergeSort' rights | rrec)
   
