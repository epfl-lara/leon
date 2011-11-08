module SortedList
  (isSorted, size
  )   where

isSorted :: [Int] -> Bool
isSorted [] = True
isSorted [_] = True
isSorted (x:y:ys) = x <= y && (isSorted (y:ys))

size :: [Int] -> Int
size [] = 0
size (_:xs) = 1 + (size xs)

contains :: [Int] -> Int -> Bool
contains [] _ = False
contains (x:xs) e = (x == e) || (contains xs e)
