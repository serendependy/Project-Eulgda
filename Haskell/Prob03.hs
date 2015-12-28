module Prob03 where

palindromeMinBound :: Integer
palindromeMinBound =  100 * 100

palindromeMaxBound :: Integer
palindromeMaxBound =  999 * 999

palindromeSolutionSpace :: [Integer]
palindromeSolutionSpace =
  [palindromeMaxBound,palindromeMaxBound-1..palindromeMinBound]

isPalindrome   :: Integer -> Bool
isPalindrome n =
  let nStr = show n
  in nStr == reverse nStr

palindromes :: [Integer]
palindromes =  filter isPalindrome palindromeSolutionSpace

is3digit   :: Integer -> Bool
is3digit n = length (show n) == 3 

isDivBy :: Integer -> Integer -> Bool
isDivBy m n = m `mod` n == 0

sqrt' :: Integer -> Integer
sqrt' =  ceiling . sqrt . fromInteger

factorPairs :: Integer -> [(Integer,Integer)]
factorPairs n = factorPairs' n (sqrt' n)
  where
    factorPairs' n x = case (x < 2, n `isDivBy` x) of
      (True, _    ) -> []
      (_   , True ) -> (x, n `div` x) : factorPairs' n (x-1)
      (_   , False) -> factorPairs' n (x-1)

bothFactors3digit :: (Integer,Integer) -> Bool
bothFactors3digit (i,j) = is3digit i && is3digit j

solution :: Integer
solution =
  let fpairs = map factorPairs palindromes
      z      = zip palindromes fpairs
  in fst . head .
     filter (not . null . snd) .
     map (\(p,fps) -> (p,takeWhile bothFactors3digit fps)) $ z

main = do
  putStrLn $ show solution
