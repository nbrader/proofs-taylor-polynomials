#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck

-- Define the factorial function
fact :: Integer -> Integer
fact 0 = 1
fact n = n * fact (n - 1)

-- Check if one number divides another
divides :: Integer -> Integer -> Bool
divides a b = b `mod` a == 0

-- Increment function (S in Peano notation)
s :: Integer -> Integer
s x = x + 1

-- Check if fact (S x0) * fact (S x1) divides fact (x0 + S x1)
checkDivision :: Integer -> Integer -> Bool
checkDivision x0 x1 = divides (fact (s x0) * fact (s x1)) (fact (x0 + s x1))

-- Test for a range of values
main :: IO ()
main = do
    let pairs = [(x0, x1) | x0 <- [0..5], x1 <- [0..5]]
    let results = [(x0, x1, checkDivision x0 x1) | (x0, x1) <- pairs]
    mapM_ print results
