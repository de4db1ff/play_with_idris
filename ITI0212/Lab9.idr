module Lab9

import Data.Fin
import Data.Vect

bool_2_fin : Bool -> Fin 2
bool_2_fin False = FZ
bool_2_fin True = FS FZ

fin_2_bool : Fin 2 -> Bool
fin_2_bool FZ = False
fin_2_bool (FS FZ) = True

map_vect : (a -> b) -> Vect n a -> Vect n b
map_vect f [] = []
map_vect f (x :: xs) = f x :: map_vect f xs

as_top : (n : Nat) -> Fin (S n)
as_top 0 = FZ
as_top (S k) = FS (as_top k)

data Tuple : (ts : Vect n Type) -> Type where
  Nil : Tuple []
  (::) : t -> Tuple ts -> Tuple (t :: ts) 

two_tuple : Pair a b -> Tuple [a, b]
two_tuple (x, y) = [x, y]

ind_pair : Pair a b -> DPair a (const b)
ind_pair (x, y) = (x ** y)

Tricky : Type
Tricky = DPair Integer (\n => if n `mod` 2 == 0 then String else Tricky)

forget_length : Vect n a -> List a
forget_length [] = []
forget_length (x :: xs) = x :: forget_length xs

learn_length : (xs : List a) -> Vect (length xs) a
learn_length [] = []
learn_length (x :: xs) = x :: learn_length xs

