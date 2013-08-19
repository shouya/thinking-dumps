
isPrime :: Integer -> Bool
isPrime x = ([] == [y | y <- [2..floor (sqrt $ fromIntegral x)], mod x y == 0])

primeSumPairs :: Integer -> [(Integer, Integer, Integer)]
primeSumPairs n =
  map makePairSum $ filter isPrimeSum [(x, y)|x <-[1..n], y <- [1..(x-1)]]
  where
    isPrimeSum (a,b) = isPrime $ a + b
    makePairSum (a,b) = (a,b,a+b)


