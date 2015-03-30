import Control.Monad.State.Lazy

data BState s a = BState { runBState :: s -> (a, s) }

instance Monad (BState s) where
  return a = BState $ \s -> (a, s)

  m >>= k  = BState $ \s'' -> let (a, s)  = runBState m s'
                                  (b, s') = runBState (k a) s''
                              in (b, s)


execBState :: BState s a -> s -> s
execBState ms sfinal = snd $ runBState ms sfinal

puta :: State String ()
puta = state $ \s -> ((), s ++ "a")

putb :: State String ()
putb = state $ \s -> ((), s ++ "b")

putaB :: BState String ()
putaB = BState $ \s -> ((), s ++ "a")

putbB :: BState String ()
putbB = BState $ \s -> ((), s ++ "b")


main :: IO ()
main = do
-- output "abb"
  print $ execState  (sequence [puta,  putb,  putb]) ""
-- output "bba" instead of "abb"
  print $ execBState (sequence [putaB, putbB, putbB]) ""
