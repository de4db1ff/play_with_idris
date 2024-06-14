module Lab10

import Data.Vect
import Data.Fin

majority: Bool -> Bool -> Bool -> Bool
majority False False _ = False
majority True True _ = True
majority False _ False = False
majority True _ True = True
majority _ False False = False
majority _ True True = True

list_majority_acc : (acc : Integer) -> List Bool -> Bool
list_majority_acc acc [] = if acc > 0 then True else False
list_majority_acc acc (False :: xs) = list_majority_acc (acc - 1) xs
list_majority_acc acc (True :: xs) = list_majority_acc (acc + 1) xs

list_majority : List Bool -> Bool
list_majority xs = list_majority_acc 0 xs

export infixr 6 >->
(>->) : (args : Vect n Type) -> (result : Type) -> Type
(>->) [] result = result
(>->) (x :: xs) result = x -> xs >-> result

ary_opp : (n : Nat) -> Type -> Type
ary_opp n a = replicate n a >-> a

weakened_by : Fin bound -> (n : Nat) -> Fin (bound + n)
weakened_by FZ n = FZ
weakened_by (FS x) n = FS (weakened_by x n)

nat_to_fin : Nat -> (bound : Nat) -> Fin bound
nat_to_fin k bound with (bound)
  nat_to_fin k bound | 0 = ?nat_to_fin_rhs_rhss_0
  nat_to_fin 0 bound | (S j) = FZ
  nat_to_fin (S k) bound | (S j) = FS (nat_to_fin k j)

as_fin : (n : Nat) -> (bound : Nat) -> Maybe (Fin bound)
as_fin n bound with (bound > n)
  as_fin n bound | False = Nothing
  as_fin n bound | True = Just (nat_to_fin n bound) 

