module Lab8

import Data.Bool.Xor
import Data.Maybe

implementation Semigroup Bool where
  (<+>) = xor

implementation Monoid Bool where
  neutral = False

implementation Semigroup (a -> a) where
  (<+>) x y = y . x

implementation Monoid (a -> a) where
  neutral = id

multiply : Monoid a => Nat -> a -> a
multiply 0 x = neutral
multiply (S k) x = (multiply k x) <+> x

consolidate : List (Maybe a) -> Maybe (List a)
consolidate [] = Just []
consolidate (Nothing :: xs) = Nothing 
consolidate ((Just x) :: xs) with (consolidate xs)
  consolidate ((Just x) :: xs) | Nothing = Nothing
  consolidate ((Just x) :: xs) | (Just y) = Just (x :: y) 

consolidate' : List (Maybe a) -> Maybe (List a)
consolidate' [] = Just []
consolidate' (Nothing :: xs) = Nothing
consolidate' (Just x :: xs) = map (x ::) (consolidate' xs) 

map0 : Applicative t => a -> t a
map0 f = pure f

map1 : Applicative t => (a -> b) -> t a -> t b
map1 f x = pure f <*> x


map2 : Applicative t => (a -> b -> c) -> t a -> t b -> t c
map2 f x y = pure f <*> x <*> y

map3 : Applicative t => (a -> b -> c -> d) -> t a -> t b -> t c -> t d
map3 f x y z = pure f <*> x <*> y <*> z

join_list : List (List a) -> List a
join_list xss = xss >>= id 
