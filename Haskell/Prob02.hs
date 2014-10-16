module Prob02 where

data Parity = Even | Odd deriving Eq

psuc :: Parity -> Parity
psuc p = case p of
    Even -> Odd
    Odd -> Even

pPlus :: Parity -> Parity -> Parity
pPlus p q = case p of
    Even -> q
    Odd  -> psuc q
    
fibs = 1 : 2 : (zipWith (+) fibs (tail fibs))
pfibs = Odd : Even : (zipWith pPlus pfibs (tail pfibs))

fibsTagged = zip fibs pfibs

solution = sum $ takeWhile (\n -> n <= 4000000) $ map (\(n,p) -> n) $ filter (\(n,p) -> p == Even) fibsTagged
