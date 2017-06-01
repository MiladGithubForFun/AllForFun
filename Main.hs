{-# LANGUAGE ExtendedDefaultRules #-}
module Main where


import Conduit
{--import Data.Conduit as C
import Data.Conduit.Combinators as CC
import Data.Conduit.Combinators.Internal as CCI
import Data.Conduit.Combinators.Stream as CCS
import Data.Conduit.Internal as CI
import Data.Conduit.Internal.Fusion as CIF
import Data.Conduit.Internal.List.Stream as CILS
import Data.Conduit.Lift as CL
import Data.Conduit.List as CL --}
import System.IO
import System.Random
import System.Random.Shuffle


main :: IO ()
main = do
 h <- readFile "result.txt" 
 runConduit $ yieldMany (lines h) .| mapC read_cand .| mapM_C print
--} 
{--
main :: IO ()
main = funct 30000

--}

funct n  =  if n <= 1 then  print u
            else do
                  c <- shuffleM u
                  print c
                  funct ( n- 1)
u = [1,2,3,4,5,6,6,7,57,8,78,9,9,62,5,44,36,37,25,2,12,32]


read_cand :: String  -> [Cand]
read_cand l = (read l) :: [Cand]

read_fun :: String -> [Integer]
read_fun l = read l

show_fun :: Integer -> String
show_fun a = show a
{--main = do
 Prelude.print $ runConduitPure $ yieldMany [1..10] .| sumC
 writeFile "input.txt" "this is a test."
 runConduitRes $ sourceFileBS "input.txt" .| sinkFile "output.txt"
 readFile "output.txt" >>= putStrLn 
 Prelude.print $ runConduitPure $ yieldMany [1..10] .| mapC (+1) .| sinkList
 putStrLn "List version:"
 print $ take 10 [1..]
 putStrLn ""
 putStrLn "Conduit version:"
 print $ runConduitPure $ yieldMany [1..] .| takeC 10 .| sinkList
 print $ runConduitPure $ yieldMany [1..] .| takeC 10 .| mapC ( *2) .| takeWhileC ( < 18) .| sinkList 
 runConduit
    $ yieldMany [1..]
    .|takeC 10
    .|mapC (*2)
    .|takeWhileC ( < 18)
    .|mapM_C print
--}

data Cand =
   A
 | B
 | C
 | D
 | E
 | F
 | G
 | H
 | I
 | J
 | K
 | L
 | M
 | N1
 | O0
 | P
 | Q0
 | R
 | S0
 | T2
 | A0
 | B0
 | C0
 | D0
 | E0
 | F0
 | G0
 | H0
 | I0
 | J0
 | K0
 | L0
 | M0
 | N10
 | O00
 | P0
 | Q00 deriving (Show, Read)

--deriving instance (Read Cand)
--deriving instance (Show Cand)


magic :: Int -> IO Int
magic x = do 
 putStrLn $ "I'm doing magic with" ++ show x
 return $ x *2


{--do
    putStrLn "List version:"
    print $ takeWhile (< 18) $ map (* 2) $ take 10 [1..]
    putStrLn ""
    putStrLn "Conduit version:"
    print $ runConduitPure
          $ yieldMany [1..]
         .| takeC 10
         .| mapC (* 2)
         .| takeWhileC (< 18)
         .| sinkList
--}
