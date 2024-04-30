module Lab5

import Lab2
import Data.List

implementation Interpolation Double where
  interpolate f = show f

show : Shape -> String
show (Circle radius) = "Circle with radius \{radius}"
show (Rectangle width height) = "Rectangle with width \{width} and height \{height}"
show (IsosTriangle base height) = "Triangle with base \{base} and height \{height}"

implementation [setwise] Eq a => Eq (List a) where
  (==) xs ys = all (\x => elem x ys) xs && all (\y => elem y xs) ys

interface PreOrd a where
  (<=) : a -> a -> Bool

implementation [divides] PreOrd Int where
  (<=) x y = not (intToBool (mod y x))

data AExpr : Num n => Type -> Type where
  V : n -> AExpr n
  Plus : AExpr n -> AExpr n -> AExpr n
  Times : AExpr n -> AExpr n -> AExpr n

eval : Num n => AExpr n -> n
eval (V n) = n
eval (Plus expr1 expr2) = eval expr1 + eval expr2
eval (Times expr1 expr2) = eval expr1 * eval expr2

implementation Num n => Eq n => Eq (AExpr n) where
  (==) expr1 expr2 = eval expr1 == eval expr2

implementation Ord n => Num n => Eq n => Ord (AExpr n) where
  (<) expr1 expr2 = eval expr1 < eval expr2

implementation Cast Bool Integer where
  cast True = 1
  cast False = 0

implementation Cast Integer Bool where
  cast 0 = False
  cast _ = True