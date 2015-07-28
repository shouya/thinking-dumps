
ex241 :: Integer -> Integer -> [(Integer, Integer, Integer)]
ex241 n s = [(a,b,c) | a <- rng, b <- rng, c <- rng, a + b + c == s]
  where rng = [1..n]
