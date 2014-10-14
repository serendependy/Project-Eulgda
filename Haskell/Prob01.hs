module Prob01 where

numbers = [1..]

div3 = \x -> x `mod` 3 == 0
div5 = \x -> x `mod` 5 == 0

terms = map (\x -> if (div3 x || div5 x) then x else 0) numbers
