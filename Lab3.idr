module Lab3

swap_pair : Pair a b -> Pair b a
swap_pair (x, y) = MkPair y x

swap_either : Either a b -> Either b a
swap_either (Left x) = Right x
swap_either (Right x) = Left x

reverse_list : List a -> List a
reverse_list [] = []
reverse_list (x :: xs) = xs ++ [x]

data Tree : (a : Type) -> Type where
    -- a tree is either empty:
    Leaf : Tree a
    -- or it is a left subtree, a current element, and a right subtree:
    Node : (l : Tree a) -> (x : a) -> (r : Tree a) -> Tree a

size : Tree a -> Nat
size Leaf = 0
size (Node l _ r) = S (size l + size r)

-- Error: Can't solve constraint between: ?prim__add_Int [no locals in scope] and ?a [no locals in scope].
-- soooo buggy :(
-- It works in the REPL though
--t1 = Node (Node Leaf 1 (Node Leaf 3 Leaf)) 5 Leaf
--t2 = Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 4 (Node (Node Leaf 5 Leaf) 6 (Node Leaf 7 Leaf))
--size t1

n_to_lu : Nat -> List Unit
n_to_lu 0 = []
n_to_lu (S k) = () :: n_to_lu k

lu_to_n : List Unit -> Nat
lu_to_n [] = 0
lu_to_n (x :: xs) = S(lu_to_n xs)
