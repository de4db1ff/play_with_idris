module Hw5

import Data.Vect

%default total

plus_one_right : {n : Nat} -> n + 1 = S n
plus_one_right {n = 0} = Refl
plus_one_right {n = (S k)} = cong S plus_one_right

transport : {fam : Nat -> Type -> Type} -> n = m -> fam n a -> fam m a
transport Refl x = x

vect_reverse : {n : Nat} -> Vect n a -> Vect n a
vect_reverse [] = []
vect_reverse (x :: xs) = transport plus_one_right {fam = Vect} ((vect_reverse xs) ++ [x]) 

dec_and : Dec p -> Dec q -> Dec (p, q)
dec_and (Yes prfp) (Yes prfq) = Yes (prfp, prfq)
dec_and (Yes prf) (No contra) = No $ contra . snd
dec_and (No contra) q = No $ contra . fst 

dec_not : Dec p -> Dec (Not p)
dec_not (Yes prf) = No (\f => f prf)
dec_not (No contra) = Yes contra

data IsEven : Nat -> Type where
  IsEvenZ  : IsEven 0
  IsEvenSS : IsEven k -> IsEven (S (S k))

%hint
prepre_even : IsEven (S (S k)) -> IsEven k
prepre_even (IsEvenSS x) = x

half : (n : Nat) -> (iseven : IsEven n) => Nat
half 0 = 0
half (S (S k)) = (S (half k))

record PlayerState where
  constructor PS
  health : Fin 11
  wealth : Fin 101

hire_healer : PlayerState -> PlayerState
hire_healer (PS health wealth) with (health < 10 && wealth >= 10)
  hire_healer (PS health wealth) | False = PS health wealth
  hire_healer (PS health wealth) | True = PS (health + 1) (wealth - 10)

infixl 10 !!
record Complex where
  constructor (!!)
  real : Double
  imaginary : Double


complex_add : Complex -> Complex -> Complex
complex_add (real_l !! imaginary_l) (real_r !! imaginary_r) = (real_l + real_r) !! (imaginary_l + imaginary_r) 

complex_mul : Complex -> Complex -> Complex
complex_mul (real_l !! imaginary_l) (real_r !! imaginary_r) = (real_l * real_r - imaginary_l * imaginary_r) !! (real_l * imaginary_r + real_r * imaginary_l)

complex_from_int : Integer -> Complex
complex_from_int n = (cast n) !! 0

%hint
impl_num_complex : Num Complex
impl_num_complex = MkNum complex_add complex_mul complex_from_int

