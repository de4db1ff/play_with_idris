data Shape : Type where
    Circle : Nat -> Shape
    Rectangle : Nat -> Nat -> Shape
    IsoTriangle : Nat -> Nat -> Shape

area : Shape -> Double
area (Circle k) = pi * (cast (k * k))
area (Rectangle k j) = (cast (k * j))
area (IsoTriangle k j) = (cast k) * (sqrt ((cast (j*j)) - (cast (k*k)) / 4)) / 2

regular : Shape -> Bool
regular (Circle k) = False
regular (Rectangle k j) = if k==j then True else False
regular (IsoTriangle k j) = if k==j then True else False

monus : Nat -> Nat -> Nat
monus Z _ = Z
monus n Z = n
monus (S k) (S j) = monus k j

even : Nat -> Bool
even Z = True
even (S Z) = False
even (S (S k)) = even k

odd : Nat -> Bool
odd Z = False
odd (S Z) = True
odd (S (S k)) = odd k

