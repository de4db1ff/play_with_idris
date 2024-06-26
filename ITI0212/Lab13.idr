module Lab13
-- 2022 Lab14
import Syntax.PreorderReasoning

%default total

congruence2 : (0 f : a -> b -> c) -> x = y -> u = v -> f x u = f y v
congruence2 f Refl Refl = Refl


%hint
plusZeroRightNeutral : (n : Nat) -> n + 0 = n
plusZeroRightNeutral 0 = Refl
plusZeroRightNeutral (S k) = cong S (plusZeroRightNeutral k)

%hint
plusSuccRightSucc : (m, n : Nat) -> S (m + n) = m + S n
plusSuccRightSucc 0 n = Refl
plusSuccRightSucc (S k) n = ind_step where
  ind_hyp : S (k + n) = k + S n
  ind_hyp = plusSuccRightSucc k n

  ind_step : S (S (k + n)) = S (k + (S n))
  ind_step = cong S ind_hyp 

%hint
plusComm : (m, n : Nat) -> m + n = n + m
plusComm 0 n = sym (plusZeroRightNeutral n)
plusComm (S k) n = goal where 
  step1 : S (k + n) = S (n + k)
  step1 = cong S (plusComm k n)

  step2 : S (n + k) = n + S k
  step2 = plusSuccRightSucc n k

  goal : S (k + n) = n + S k
  goal = trans step1 step2


-- preorder reasoning
plusComm' : (m, n : Nat) -> m + n = n + m
plusComm' 0 n = Calc $
  |~ 0 + n ~~ n     ...(Refl)
           ~~ n + Z ...(sym $ plusZeroRightNeutral n)

plusComm' (S k) n = Calc $
  |~ S (k + n) ~~ S (n + k) ...(cong S $ plusComm k n)
               ~~ n + S k   ...(plusSuccRightSucc n k)


data IsPrefix : (xs : List a) -> (ys : List a) -> Type where
  IsPrefixNil : IsPrefix [] ys
  IsPrefixCons : IsPrefix xs ys -> IsPrefix (x :: xs) (x :: ys)

%hint
consCong : {0 xs , ys : List a } -> xs = ys -> x :: xs = x :: ys
consCong prf = cong (x ::) prf

isPrefixAntisymm : {xs, ys : List a} -> IsPrefix xs ys -> IsPrefix ys xs -> xs = ys
isPrefixAntisymm IsPrefixNil IsPrefixNil = Calc $
  |~ [] ~~ []     ...(Refl)
isPrefixAntisymm {xs = (x :: xs)} {ys = (x :: ys)} (IsPrefixCons prf1) (IsPrefixCons prf2) = Calc $
  |~ x :: xs ~~ x :: ys    ...(consCong (isPrefixAntisymm prf1 prf2))
  
