module Lab2

xor : Bool -> Bool -> Bool
xor False False = False
xor False True = True
xor True False = True
xor True True = False

data Prob : Type where
  Definitely : Prob
  Likely     : Prob
  Doubtful   : Prob
  Impossible : Prob

not : Prob -> Prob
not Definitely = Impossible
not Likely = Doubtful
not Doubtful = Likely
not Impossible = Definitely

and : Prob -> Prob -> Prob
and Impossible _ = Impossible
and _ Impossible = Impossible
and Doubtful _ = Doubtful
and _ Doubtful = Doubtful
and Likely _ = Likely
and _ Likely = Likely
and _ _ = Definitely

mul : Nat -> Nat -> Nat
mul 0 j = 0
mul (S k) j = (mul k j) + j

factorial : Nat -> Nat
factorial 0 = 1
factorial (S n) = mul (S n) (factorial n) 

data Shape : Type where
  Circle : (radius : Double) -> Shape
  Rectangle : (width : Double) -> (height : Double) -> Shape
  IsosTriangle : (base : Double) -> (height : Double) -> Shape

area : Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (IsosTriangle b h) = 0.5 * b * h