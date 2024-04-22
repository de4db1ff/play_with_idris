module Hw1

import Lab3

fib : Nat -> Nat
fib Z = 0
fib (S Z) = 1
fib (S (S k)) = fib k + fib (S k)

exp : Nat -> Nat -> Nat
exp k 0 = 1
exp k (S j) = k * exp k j

fun1 : Either a a -> a
fun1 (Left x) = x
fun1 (Right x) = x

fun2 : Pair (Pair a b) c -> Pair a (Pair b c)
fun2 x = (fst (fst x), (snd (fst x), snd x))

fun3 : Pair a (Either b c) -> Either (Pair a b) (Pair a c)
fun3 (x, (Left y)) = Left (x, y)
fun3 (x, (Right y)) = Right (x, y)

reflect : Tree a -> Tree a
reflect Leaf = Leaf
reflect (Node l x r) = Node r x l

greatest : List Integer -> Maybe Integer
greatest [] = Nothing
greatest (x :: xs) = max (Just x) (greatest xs)

forward : Maybe a -> Either Unit a
forward Nothing = Left ()
forward (Just x) = Right x

backward : Either Unit a -> Maybe a
backward (Left x) = Nothing
backward (Right x) = Just x

zip_tree : (a -> b -> c) -> Tree a -> Tree b -> Tree c
zip_tree f Leaf _ = Leaf
zip_tree f (Node l x r) Leaf = Leaf
zip_tree f (Node l x r) (Node y z w) = Node (zip_tree f l y) (f x z) (zip_tree f r w)

flatten_list : List (List a) -> List a
flatten_list [] = []
flatten_list (x :: []) = x
flatten_list (x :: (y :: xs)) = x ++ y ++ flatten_list xs

fold_list : (n : t) -> (c : a -> t -> t) -> List a -> t
fold_list n c [] = n
fold_list n c (x :: xs) = c x (fold_list n c xs)

flatten_list' : List (List a) -> List a
flatten_list' = fold_list [] (++)