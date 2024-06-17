module Lab11

%default total

data (<=) : (p : Nat) -> (n : Nat) -> Type where
  LeZ : 0 <= n
  LeS : p <= n -> S p <= S n

leTrans : m <= n -> n <= p -> m <= p
leTrans {m = 0} {n = n} {p = p} LeZ y = LeZ
leTrans {m = (S p)} {n = (S n)} {p = (S p)} (LeS x) (LeS y) = LeS $ leTrans x y

leSucc : (n : Nat) -> n <= S n
leSucc 0 = LeZ
leSucc (S k) = LeS $ leSucc k

leWeakRight : (m, n : Nat) -> m <= n -> m <= S n
leWeakRight 0 n x = LeZ
leWeakRight (S k) (S j) (LeS x) = LeS (leWeakRight k j x)

leWeakLeft : (m, n : Nat) -> S m <= n -> m <= n
leWeakLeft 0 n x = LeZ
leWeakLeft (S k) (S j) (LeS x) = LeS (leWeakLeft k j x)

zeroPlusRight : (m, n : Nat) -> m + 0 <= m + n
zeroPlusRight 0 n = LeZ
zeroPlusRight (S k) 0 = LeS (zeroPlusRight k 0)
zeroPlusRight (S k) (S j) = LeS (zeroPlusRight k (S j))

zeroPlusLeft : (m, n : Nat) -> 0 + n <= m + n
zeroPlusLeft _ 0 = LeZ
zeroPlusLeft 0 (S k) = LeS $ zeroPlusLeft 0 k
zeroPlusLeft (S k) (S j) = LeS $ leTrans (leSucc j) (zeroPlusLeft k (S j))

succPlusRight : (m, n : Nat) -> m + n <= m + S n
succPlusRight 0 n = leSucc n
succPlusRight (S k) n = LeS (succPlusRight k n)

succPlusLeft : (m, n : Nat) -> m + n <= S m + n
succPlusLeft 0 n = leSucc n
succPlusLeft (S k) n = LeS $ leSucc (plus k n)

data IsPrefix : ( xs : List a ) -> ( ys : List a ) -> Type where
  IsPrefixNil : IsPrefix [] ys
  IsPrefixCons : IsPrefix xs ys -> IsPrefix ( z :: xs ) ( z :: ys )

data IsLt : (p : List a) -> (q : List a) -> Type where
  IsLtNil : IsLt [] q
  IsLtCons : IsLt p q -> IsLt (x :: p) (x :: q)

ltLen : IsLt n m -> IsLt (x :: n) (x :: m)  
ltLen IsLtNil = IsLtCons IsLtNil
ltLen (IsLtCons y) = IsLtCons (ltLen y)

prefixLess : (IsPrefix xs ys) -> (IsLt xs ys)
prefixLess IsPrefixNil = IsLtNil
prefixLess (IsPrefixCons x) = IsLtCons (prefixLess x)

induction_list : (prop : List a -> Type) ->
            (base_case : prop []) ->
            (induction_step : (x : a) -> (xs : List a) -> prop xs -> prop (x :: xs)) ->
            (l : List a) -> prop l
induction_list prop base_case induction_step [] = base_case
induction_list prop base_case induction_step (x :: xs) = induction_step x xs (induction_list prop base_case induction_step xs)

data (<*) : (p : List a) -> (q : List a) -> Type where
  LeNil : [] <* q 
  LeCons : p <* q -> (x :: p) <* (z :: q)

proofLess : (x : a) -> (xs : List a) -> xs <* (x :: xs) 
proofLess x [] = LeNil
proofLess x (y :: ys) = LeCons (proofLess y ys) 

proofLess' : (x : a) -> (xs : List a) -> xs <* (x :: xs) 
proofLess' x xs = induction_list (\list => list <* x :: list) LeNil ?ind_step xs where
  ind_step : (x : a) -> (xs : List a) -> xs <* (x :: xs) -> (x :: xs) <* (x :: (x :: xs))
  ind_step x xs y = LeCons y

{-
  weird bug...
  Error: While processing right hand side of proofLess'. When unifying:
      (x : a) -> (xs : List a) -> xs <* (x :: xs) -> (x :: xs) <* (x :: (x :: xs))
  and:
      (x : a) -> (xs : List a) -> xs <* (x :: xs) -> (x :: xs) <* (x :: (x :: xs))
  Mismatch between: x and x.
-}
