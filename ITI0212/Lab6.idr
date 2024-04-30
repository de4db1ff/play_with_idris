module Lab6

import Data.Colist

coL : List a -> Colist a
coL [] = []
coL (x :: xs) = x :: coL xs

uncoL : Colist a -> List a
uncoL [] = []
uncoL (x :: xs) = x :: uncoL xs

colist : Colist Nat
colist = 0 :: colist

data  Conat : Type  where
	Zero  :  Conat
	Succ  :  Inf Conat -> Conat

length : Colist a -> Conat
length [] = Zero
length (x :: xs) = Succ (length xs)

filter : (a -> Bool) -> Colist a -> Colist a
filter f [] = []
filter f (x :: xs) with (f x == True)
  _ | True = x :: filter f xs
  _ | False = filter f xs

f : a -> bool
f = f

unroll : (a -> a) -> a -> Stream a
unroll f x = x :: unroll f (f x)

zipSL : (a -> b -> c) -> Stream a -> List b -> List c
zipSL f (x :: xs) [] = []
zipSL f (x :: xs) (y :: ys) = f x y :: zipSL f xs ys


add : Conat -> Conat -> Conat
add Zero n  =  n
add (Succ m) n  =  Succ (add m n)

-- not total
mul' : Conat -> Conat -> Conat
mul' Zero _ = Zero
mul' _ Zero = Zero
mul' (Succ x) (Succ y) = Succ (mul' x y) `add` (add x y)

-- total but cannot pass the totality checker
mul : Conat -> Conat -> Conat
mul Zero _ = Zero
mul _ Zero = Zero
mul (Succ x) (Succ y) = let mul_minus_1 = \x, y => Succ (mul x y) in
                        add (add x y) (mul_minus_1 x y)

-- pass the totality checker, though not elegant
mul_minus_1' : Conat -> Conat -> Conat
mul_minus_1' Zero _ = Zero
mul_minus_1' _ Zero = Zero
mul_minus_1' (Succ x) (Succ y) = Succ (mul_minus_1' x y)

mul'' : Conat -> Conat -> Conat
mul'' Zero _ = Zero
mul'' _ Zero = Zero
mul'' (Succ x) (Succ y) = mul_minus_1' x y `add` (add x y)


coN  :  Nat -> Conat
coN Z  =  Zero
coN (S n)  =  Succ (coN n)

uncoN : Conat -> Nat
uncoN Zero = Z
uncoN (Succ n) = S (uncoN n)

implementation Num Conat where
  (+) = add
  (*) = mul
  fromInteger = coN . fromInteger

infinity : Conat
infinity = Succ infinity