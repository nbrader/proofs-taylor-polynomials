#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck

import Test.QuickCheck

-- Define the factorial function
fact :: Integer -> Integer
fact 0 = 1
fact n = n * fact (n - 1)

-- Successor function (S in Peano notation)
s :: Integer -> Integer
s x = x + 1

-- Compute the left-hand side of the equation
lhs :: Integer -> Integer -> Double
lhs x0 x1 = 1 / (fromIntegral (fact (s x0)) * fromIntegral (fact (s x1)))

-- Compute the right-hand side of the equation
rhs :: Integer -> Integer -> Double
rhs x0 x1 = fromIntegral (s (x0 + s x1) * fact (x0 + s x1)) 
            / (fromIntegral (fact (s x0) * fact (s x1)) * fromIntegral (s (x0 + s x1)) * fromIntegral (fact (x0 + s x1)))

-- Property to check if lhs and rhs are approximately equal
prop_divisionEquality :: Integer -> Integer -> Property
prop_divisionEquality x0 x1 = 
    (x0 >= 0 && x0 <= 10 && x1 >= 0 && x1 <= 10) ==> -- Limit range of x0 and x1
    abs (lhs x0 x1 - rhs x0 x1) < 1e-9

-- Main function to run the QuickCheck test
main :: IO ()
main = quickCheck prop_divisionEquality
