module Hw2

import Data.Colist
import Data.Stream
import Data.String
import Lab6

interface Queue (queue: Type -> Type) where
  emp : queue a
  push : a -> queue a -> queue a
  pop : queue a -> Maybe (Pair a (queue a))

implementation Queue List where
  emp = []
  push elm queue = queue ++ [elm]
  pop [] = Nothing
  pop (elm :: queue) = Just (elm, queue)

implementation Cast (List a) (Colist a) where
  cast [] = []
  cast (x :: xs) = x :: cast xs

implementation Cast (Stream a) (Colist a) where
  cast (x :: y) = x :: cast y

pred : Nat -> Maybe Nat
pred 0 = Nothing
pred (S k) = Just k

unroll : (a -> Maybe a) -> a -> Colist a
unroll f x with (f x)
  unroll f x | Nothing = singleton x
  unroll f x | (Just y) = x :: (unroll f y)

partial
implementation Eq Conat where
  (==) Zero Zero = True
  (==) (Succ x) (Succ y) = x == y
  (==) _ _ = False

partial
implementation Ord Conat where
  (<) Zero (Succ x) = True
  (<) (Succ x) (Succ y) = x < y
  (<) _ _ = False

Infinity = Succ Infinity

joinIO : IO (IO a) -> IO a
joinIO x = x >>= id

mapIO : (a -> b) -> IO a -> IO b
mapIO f x = x >>= 
  \ res => pure $ f res

eitherIO : Either (IO a) (IO b) -> IO (Either a b)
eitherIO x with (x)
  eitherIO x | (Left comp) = comp >>= 
    \res => pure $ Left res
  eitherIO x | (Right comp) = do
    res <- comp
    pure $ Right res

bothIO : Pair (IO a) (IO b) -> IO (Pair a b)
bothIO (x, y) = do
 res1 <- x
 res2 <- y
 pure $ (res1, res2)

get_number : IO (Maybe Integer)
get_number = do
  putStr "Please enter a number: "
  input <- getLine
  pure $ parsePositive input

insist : IO (Maybe a) -> IO a
insist comp = do
  res <- comp
  case res of
       Nothing => insist comp
       (Just x) => pure x

