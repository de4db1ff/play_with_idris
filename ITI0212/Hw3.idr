module Hw3

import Data.Fin
import Data.Vect

implementation [pointwise] Monoid a => Semigroup (List a) where
  (<+>) (x :: xs) (y :: ys) = (x <+> y) :: xs <+> ys
  (<+>) [] ys = ys
  (<+>) xs [] = xs

update_list : (new : a) -> (i : Nat) -> List a -> Maybe (List a)
update_list new _ [] = Nothing
update_list new 0 (x :: xs) = Just (new :: xs)
update_list new (S k) (x :: xs) = map (x ::) $ update_list new k xs 

update_vect : (new : a) -> (i : Fin n) -> Vect n a -> Vect n a
update_vect new FZ (x :: xs) = new :: xs 
update_vect new (FS n) (x :: xs) = x :: update_vect new n xs

monadify : Monad m => (a -> b -> c) -> m a -> m b -> m c
monadify f ma mb = do 
  a <- ma
  b <- mb
  pure $ f a b

data Tuple : (ts : Vect n Type) -> Type where
  Nil  : Tuple []
  (::) : t -> Tuple ts -> Tuple (t :: ts)

concat_tuple : Tuple ts_1 -> Tuple ts_2 -> Tuple (ts_1 ++ ts_2)
concat_tuple [] ys = ys
concat_tuple (x :: z) ys = x :: concat_tuple z ys

as_tuple : Vect n a -> Tuple (replicate n a) 
as_tuple [] = []
as_tuple (x :: xs) = x :: as_tuple xs

Either' : Type -> Type -> Type
Either' a b = DPair Bool (\ x => if x then b else a)

from_either : Either a b -> Either' a b
from_either (Left x) = (False ** x)
from_either (Right x) = (True ** x)

to_either : Either' a b -> Either a b
to_either ((False ** snd)) = Left snd
to_either ((True ** snd)) = Right snd

Object : Type
Object = DPair Type id

wrap : {a : Type} -> (x : a) -> Object
wrap x = (a ** x)

unwrap : (obj : Object) -> fst obj
unwrap x = snd x

data Error : Type where
  MkError : String -> Error

(+) : Object -> Object -> Object
(+) ((Integer ** val1)) ((Integer ** val2)) = (Integer ** val1 + val2)
(+) ((String ** val1)) ((String ** val2)) = (String ** val1 ++ val2)
(+) ((Bool ** val1)) ((Bool ** val2)) = (Bool ** val1 && val2)
(+) any_val1 any_val2 = (Error ** (MkError "type error"))

