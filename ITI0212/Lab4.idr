module Lab4

map_maybe : (a -> b) -> Maybe a -> Maybe b
map_maybe f Nothing = Nothing
map_maybe f (Just x) = Just (f x)

transform : (f : a -> a) -> (index : Nat) -> List a -> List a
transform f _ [] = []
transform f 0 (x :: xs) = f x :: xs
transform f (S k) (x :: xs) = x :: transform f k xs

ignore_lowerCaseVowels : String -> String
ignore_lowerCaseVowels str = pack (filter (\x =>  x /= 'a' && x /= 'e' && x /= 'i' && x /= 'o' && x /= 'u') (unpack str))

elem' : Eq a => a -> List a -> Bool
elem' x [] = False
elem' x (y :: xs) = x == y || elem' x xs

fold_nat : (z : t) -> (s : t -> t) -> Nat -> t
fold_nat z s 0 = z
fold_nat z s (S k) = s (fold_nat z s k)

fold_list : (z : t) -> (s : a -> t -> t) -> List a -> t
fold_list z s [] = z
fold_list z s (x :: xs) = s x (fold_list z s xs)

mult' : Nat -> Nat -> Nat
mult' k = fold_nat 0 (+k)

n_to_lu : Nat -> List Unit
n_to_lu = fold_nat [] (\x => () :: x)

lu_to_n : List Unit -> Nat
lu_to_n = fold_list 0 (\x , y => S y)

fold_bool : (n : t) -> (y : t) -> Bool -> t
fold_bool n y False = n
fold_bool n y True = y
