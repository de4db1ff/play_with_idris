module Lab7

import Data.String
import System.File

concat_strings : IO String
concat_strings = do
	putStr "Please enter the first sentence :"
	input1 <- getLine
	putStr "Please enter the second sentence :"
	input2 <- getLine
	pure $ input1 ++ input2

concat_strings' : IO String
concat_strings' =  putStr "Please enter the first sentence :" >>=
                   const getLine >>=
                   \input1 =>	putStr "Please enter the second sentence :" >>= 
                   const getLine >>=
                   \input2 => pure $ input1 ++ input2

add_after : Integer -> IO (Maybe Integer)
add_after i = do
  putStrLn "Please enter a number:"
  input <- getLine
  case (parsePositive input) of
    Nothing => pure Nothing
    Just j  => pure $ Just $ i + j

count_words : IO Unit
count_words = do 
  putStrLn "Enter some text:"
  input <- getLine
  putStrLn $ "You have typed " ++ (cast $ List.length $ words input) ++ " words."

get_lines : IO (List String)
get_lines = do
  putStrLn "Please enter a sentence"
  input <- getLine
  case trim input == "done" of
       False => do 
         inputs <- get_lines
         pure $ input :: inputs
       True => pure [] 

get_only_ints : IO (List Integer)
get_only_ints = do 
  putStrLn "Please enter a sentence"
  input <- getLine
  case (parsePositive input) of
       Nothing => case trim input == "done" of
                       False => get_only_ints 
                       True => pure []
       (Just x) => do 
         inputs <- get_only_ints
         pure $ x :: inputs

dictate : IO ()
dictate = do 
  content <- get_lines
  putStr "Enter filename:"
  filename <- getLine
  result <- writeFile{io=IO} filename $ unwords content
  case result of
       (Left error) => print error 
       (Right success) => putStrLn "success!"
