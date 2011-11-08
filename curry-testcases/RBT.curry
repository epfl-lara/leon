module RBT
  (Tree, size, isRBT
  )   where

--- The colors of a node in a red-black tree.
data Color = Red | Black

--- The structure of red-black trees.
data Tree = Node Color Int Tree Tree
            | Empty

max :: Int -> Int -> Int
max a b = if (a > b) then a else b

size :: Tree -> Int
size Empty = 0
size (Node _ _ l r) = 1 + (size l) + (size r)

isBlack :: Tree -> Bool
isBlack Empty = True
isBlack (Node c _ _ _) = c==Black

redNodesHaveBlackChildren :: Tree -> Bool
redNodesHaveBlackChildren Empty = True
redNodesHaveBlackChildren (Node Black _ l r) = 
  (redNodesHaveBlackChildren l) && (redNodesHaveBlackChildren r)
redNodesHaveBlackChildren (Node Red _ l r) =
  (isBlack l) && (isBlack r) && (redNodesHaveBlackChildren l) && (redNodesHaveBlackChildren r)

blackBalanced :: Tree -> Bool
blackBalanced Empty = True
blackBalanced (Node _ _ l r) =
  (blackBalanced l) && (blackBalanced r) && (blackHeight l == blackHeight r)

blackHeight :: Tree -> Int
blackHeight Empty = 0
blackHeight (Node Black _ l _) = 1 + (blackHeight l)
blackHeight (Node Red _ l _) = blackHeight l

isRBT :: Tree -> Bool
isRBT t = (blackBalanced t) && (redNodesHaveBlackChildren t)

valuesWithin :: Tree -> Int -> Bool
valuesWithin Empty _ = True
valuesWithin (Node _ v l r) bound =
  0 <= v && v <= bound && (valuesWithin l bound) && (valuesWithin r bound)
