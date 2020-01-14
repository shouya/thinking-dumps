
-- stack script
import           Prelude (putStrLn, IO)
import           Control.Category
import           Control.Arrow
import           Data.Either
import           Control.Applicative

newtype Apply f a b = Apply (f (a -> b))

-- first of all, Apply forms a category (similar to Kleisli category)
--
instance (Applicative f) => Category (Apply f) where
  id = Apply (pure id)

  (Apply f) . (Apply g) = Apply (liftA2 compose f g)
    where
      compose f' g' x = f' (g' x)

-- then we can see that Apply is also an Arrow
instance (Applicative f) => Arrow (Apply f) where
  arr f = Apply (pure f)

  first (Apply fbc) = Apply (bc2bdcd <$> fbc)
    where
      bc2bdcd bc (b, d) = (bc b, d)

instance (Applicative f) => ArrowChoice (Apply f) where
  left (Apply fbc) = Apply (bc2ebdecd <$> fbc)
    where
      bc2ebdecd bc (Left b) = Left (bc b)
      bc2ebdecd _ (Right d) = Right d



main :: IO ()
main = putStrLn "type checks!"
