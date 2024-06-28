module Lab15

import Data.Fin
import Decidable.Equality

%default total 

subtract_uf : Nat -> Nat -> Nat
subtract_uf 0 j = 0
subtract_uf (S k) 0 = S k
subtract_uf (S k) (S j) = subtract_uf k j

subtract_maybe : Nat -> Nat -> Maybe Nat
subtract_maybe 0 0 = Just 0
subtract_maybe 0 (S k) = Nothing
subtract_maybe (S k) 0 = Just (S k)
subtract_maybe (S k) (S j) = subtract_maybe k j

subtract_fin : (m : Nat) -> (n : Fin (S m)) -> Nat
subtract_fin 0 FZ = 0
subtract_fin (S k) FZ = S k
subtract_fin (S k) (FS x) = subtract_fin k x

subtract_lte : (m : Nat) -> (n : Nat) -> (inbounds : n `LTE` m) -> Nat
subtract_lte m 0 LTEZero = m
subtract_lte (S k) (S j) (LTESucc x) = subtract_lte k j x

subtract_cst : (m : Nat) -> (n : Nat) -> (inbounds : n `LTE` m) => Nat
subtract_cst m 0 {inbounds = LTEZero} = m
subtract_cst (S m) (S n) {inbounds = (LTESucc x)} = subtract_cst m n 

-- lemma
%hint
pre_lte : (S n) `LTE` (S m) -> n `LTE` m
pre_lte (LTESucc x) = x

subtract_cst' : (m : Nat) -> (n : Nat) -> (inbounds : n `LTE` m) => Nat
subtract_cst' m 0 = m
subtract_cst' 0 (S n) impossible 
subtract_cst' (S m) (S n) = subtract_cst' m n {inbounds = pre_lte inbounds}


decide_lte : (n , m : Nat) -> Dec (n `LTE` m)
decide_lte 0 m = Yes LTEZero
decide_lte (S k) 0 = No uninhabited
decide_lte (S k) (S j) = case decide_lte k j of
                              Yes prf => Yes (LTESucc prf)
                              No contra => No (contra . pre_lte)

%hint
pair_lemma1 : x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2) 
pair_lemma1 Refl Refl = Refl

%hint
pair_lemma2 : (x1, y1) = (x2, y2) -> (x1 = x2, y1 = y2)
pair_lemma2 Refl = (Refl, Refl) 

implementation DecEq a => DecEq b => DecEq (Pair a b) where
  decEq (x1, y1) (x2, y2) with (decEq x1 x2)
    decEq (x1, y1) (x2, y2) | (Yes prf) with (decEq y1 y2)
      decEq (x1, y1) (x2, y2) | (Yes prfl) | (Yes prfr) = Yes (pair_lemma1 prfl prfr)
      decEq (x1, y1) (x2, y2) | (Yes prfl) | (No contrar) = No (contrar . snd . pair_lemma2)
    decEq (x1, y1) (x2, y2) | (No contra) with (decEq y1 y2)
      decEq (x1, y1) (x2, y2) | (No contral) | (Yes prfr) = No (contral . fst . pair_lemma2)
      decEq (x1, y1) (x2, y2) | (No contral) | (No contralr) = No (contral . fst . pair_lemma2)

-- the law of the excluded middle is not not deciable :)
nndec_lem : Not (Not (Dec (Either p (Not p))))
nndec_lem f = f (No (\x => f (Yes x)))

