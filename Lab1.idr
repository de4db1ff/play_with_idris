small : Integer
small = 7

large : Integer
large = small * 6

medium : Integer

average : Double -> Double -> Double
average x y = (x + y) / 2

medium = cast (average (cast large) (cast small))