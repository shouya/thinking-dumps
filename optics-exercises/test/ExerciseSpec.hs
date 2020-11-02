module ExerciseSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Control.Lens

import Exercise

spec :: Spec
spec = do
  ex1LawsSpec

instance Arbitrary Err where
  arbitrary = do
    oneof [ExitCode <$> arbitrary, ReallyBadError <$> arbitrary]

ex1LawsSpec :: Spec
ex1LawsSpec = do
  it "1.1 get-set law should fail" $ expectFailure $
    \s -> set unlawful2 (view unlawful2 s) s == s
  it "1.1 set-set law should fail" $ expectFailure $
    \b s -> set unlawful3 b (set unlawful3 b s) == set unlawful3 b s

  -- cheating with quick check
  it "2.1 test get-set law for msg" $ property $
    \s -> set msg (view msg s) s == s
  it "2.2 test set-set law for msg" $ expectFailure $
    \b s -> set msg b (set msg b s) == s

  it "3.1 test set-set law for msg" $ property $
    \b s -> set msg' b (set msg' b s) == set msg' b s
  it "3.2 test set-get law for msg" $ property $
    \b s -> view msg' (set msg' b s) == b
  it "3.3 test get-set law for msg" $ expectFailure $
    \s -> set msg' (view msg' s) s == s
