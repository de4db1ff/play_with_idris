module Hw4

import Data.List
import Data.Vect
import Syntax.PreorderReasoning

%default total

data (<=) : (p : Nat) -> (n : Nat) -> Type where
  LeZ : 0 <= n
  LeS : p <= n -> S p <= S n

data IsSorted : List Nat -> Type where
  NilSort : IsSorted []
  SinglSort : IsSorted [x]
  ConsSort : IsSorted (y :: ys) -> x <= y -> IsSorted (x :: y :: ys)

is_sorted_0123 : IsSorted [0, 1, 2, 3]
is_sorted_0123 = ConsSort (ConsSort (ConsSort SinglSort (LeS (LeS LeZ))) (LeS LeZ)) LeZ 

is_sorted_succ : (xs : List Nat) -> IsSorted xs -> IsSorted (map S xs)
is_sorted_succ [] NilSort = NilSort
is_sorted_succ [x] SinglSort = SinglSort
is_sorted_succ (x1 :: (x2 :: xs)) (ConsSort sorted le) = ConsSort (is_sorted_succ (x2 :: xs) sorted) (LeS le)

is_sorted_cst : (lg, val : Nat) -> IsSorted (replicate lg val)
is_sorted_cst 0 val = NilSort
is_sorted_cst (S 0) val = SinglSort
is_sorted_cst (S (S k)) val = ConsSort (is_sorted_cst (S k) val) refl_lemma where
  refl_lemma : {n : Nat} -> n <= n
  refl_lemma {n = 0} = LeZ
  refl_lemma {n = (S j)} = LeS refl_lemma


and_not_or : (a, b) -> Not (Either (Not a) (Not b))
and_not_or (x, y) (Left z) = z x
and_not_or (x, y) (Right z) = z y

or_not_and : (Either a b) -> Not (Not a, Not b)
or_not_and (Left x) (y, z) = y x
or_not_and (Right x) (y, z) = z x

not_or : Not (Either a b) -> (Not a, Not b)
not_or f = (\x => f (Left x), \x => f (Right x))

not_or' : (Not a, Not b) -> Not (Either a b) 
not_or' (x, z) (Left y) = x y
not_or' (x, z) (Right y) = z y

not_and : Not (a, b) -> Either (Not a) (Not b)
not_and f = ?not_and_rhs
-- unprovable ? equivalent to the halting problem

not_and' : Either (Not a) (Not b) -> Not (a, b)
not_and' (Left x) (y, z) = x y
not_and' (Right x) (y, z) = x z

forall_or : {t : Type} -> {p, q : t -> Type} -> Either ((v : t) -> (p v)) ((v : t) -> (q v)) -> ((v : t) -> Either (p v) (q v))
forall_or (Left x) v = Left (x v)
forall_or (Right x) v = Right (x v)

exist_p_not_p : {a : Type} -> {p : a -> Type} -> ((DPair a p), (DPair a (Not . p))) -> Not $ Either ((elm : a) -> p elm) ((elm : a) -> (Not . p) elm)
exist_p_not_p ((elm1 ** prf_pos), (elm2 ** prf_neg)) (Left prf_all) = prf_neg (prf_all elm2)
exist_p_not_p ((elm1 ** prf_pos), (elm2 ** prf_neg)) (Right prf_all_not) = prf_all_not elm1 prf_pos

lem_to_dne : Either a (Not a) -> Not (Not a) -> a
lem_to_dne (Left x) f = x
lem_to_dne (Right x) f = whatever $ f x where
  whatever : Void -> a
  whatever x impossible

not_not_lem : Not (Not (Either a (Not a)))
not_not_lem f = f $ Right (\x => f (Left x))

same_length : {xs : Vect m a} -> {ys : Vect n a} -> xs = ys -> length xs = length ys
same_length Refl = Refl

same_elments : {xs , ys : Vect n a} -> xs = ys -> index i xs = index i ys
same_elments Refl = Refl

different_heads : {xs , ys : Vect n a} -> Not (x = y) -> Not (x :: xs = y :: ys)
different_heads prf_neq Refl = prf_neq Refl

interface Functor t => FunctorV (t : Type -> Type) where
  pres_idty : (xs : t a) -> map Prelude.id xs = xs
  pres_comp : (f : a -> b) -> (g : b -> c) -> (xs : t a) -> map (g . f) xs = (map g . map f) xs

FunctorV List where
  pres_idty [] = Refl
  pres_idty (x :: xs) = cong (x::) $ pres_idty xs where

  pres_comp f g [] = Refl
  pres_comp f g (x :: xs) = cong (g (f x)::) goal where
    goal : {xs : List a} -> mapImpl (\x => g (f x)) xs = mapImpl g (mapImpl f xs)
    goal {xs = []} = Refl
    goal {xs = (y :: xs)} = cong (g (f y)::) goal



rev : List a -> List a
rev [] = []
rev (x :: xs) = rev xs ++ [x]

-- lemma
rev_inv_cons : (x : a) -> (xs : List a) -> rev (xs ++ [x]) = x :: rev xs
rev_inv_cons x [] = Refl
rev_inv_cons x (y :: xs) = 
  let
    IH = rev_inv_cons x xs
  in Calc $
    |~ rev ((y :: xs) ++ [x])
    ~~ rev (xs ++ [x]) ++ [y] ...(Refl)
    ~~ (x :: rev xs) ++ [y]   ...(cong (++[y]) IH)
    ~~ x :: (rev xs ++ [y])   ...(Refl)
    ~~ x :: rev (y :: xs)     ...(Refl)


rev_inv : (xs : List a) -> rev (rev xs) = xs
rev_inv [] = Refl
rev_inv (x :: xs) = 
  let 
    IH = rev_inv xs
  in Calc $
    |~ rev (rev (x :: xs))
    ~~ rev (rev xs ++ [x]) ...(Refl)
    ~~ x :: rev (rev xs)   ...(rev_inv_cons x (rev xs)) 
    ~~ x :: xs             ...(cong (x::) IH)
