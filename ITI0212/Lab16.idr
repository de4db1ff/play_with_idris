module Lab16

import Data.String
import Data.Nat

record Rational where
  constructor (//)
  numerator   : Nat
  denominator : Nat
infixl 10 //

implementation Eq Rational where
  (==) (numerator_l // denominator_l) (numerator_r // denominator_r) = numerator_l * denominator_r == numerator_r * denominator_l

implementation Num Rational where
  (+) (numerator_l // denominator_l) (numerator_r // denominator_r) = (numerator_l * denominator_r + numerator_r * denominator_l) // (denominator_l * denominator_r)
  (*) (numerator_l // denominator_l) (numerator_r // denominator_r) = (numerator_l * numerator_r) // (denominator_l * denominator_r)
  fromInteger n = (cast n // 1)

record Post where
  constructor MkPost
  text : String
  likes : Nat
  comments : List Post

partial
implementation Show Post where
  show p = 
    let
      rec = foldr (++) "" (map show p.comments)
    in
      p.text ++ "\n" ++
      "Likes: " ++ show p.likes ++ "\n" ++
      indent rec
    where
      indent : String -> String
      indent = unlines . map (" " ++) . lines
      
new_post : String -> Post
new_post text = MkPost text Z []

like_post : Post -> Post
like_post post = {likes $= S} post 

react_post : String -> Post -> Post
react_post text post = {comments $= ((new_post text)::)} post

record RoseTree (t : Type) where
  constructor Node
  val : t
  nodes : List (RoseTree t)

is_even : Nat -> Bool
is_even 0 = True
is_even (S k) = not (is_even k) 

implementation Functor RoseTree where
  map f tree = {val $= f, nodes $= map (map f)} tree 
-- totality checker would complain 

index : List Nat -> RoseTree a -> Maybe a
index [] (Node val nodes) = Just val
index (x :: xs) (Node val nodes) with (getAt x nodes)
  index (x :: xs) (Node val nodes) | Nothing = Nothing
  index (x :: xs) (Node val nodes) | (Just node) = index xs node 

%hint
mul_non_zero : (nzm : NonZero m) -> (nzn: NonZero n) -> NonZero (mult m n) 
mul_non_zero SIsNonZero SIsNonZero = SIsNonZero

record Rational' where
  constructor (///)
  numerator   : Nat
  denominator : Nat
  {auto nz : NonZero denominator} 
infixl 10 ///

implementation Eq Rational' where
  (==) ( (///) numerator_l denominator_l {nz = nzl}) ((///) numerator_r denominator_r {nz = nzr}) = numerator_l * denominator_r == numerator_r * denominator_l

implementation Num Rational' where
  (+) ((///) numerator_l denominator_l {nz = nzl}) ((///) numerator_r denominator_r {nz = nzr}) = (///) (numerator_l * denominator_r + numerator_r * denominator_l) (denominator_l * denominator_r) {nz = mul_non_zero nzl nzr}
  (*) ((///) numerator_l denominator_l {nz = nzl}) ((///) numerator_r denominator_r {nz = nzr}) = (///) (numerator_l * numerator_r) (denominator_l * denominator_r) {nz = mul_non_zero nzl nzr}
  fromInteger n = (cast n /// 1)
  

