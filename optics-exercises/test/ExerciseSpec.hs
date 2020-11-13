module ExerciseSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Control.Lens
import Control.Lens.Properties

import Exercise

spec :: Spec
spec = do
  exercise_Laws
  exercise_VirtualFields
  exercise_SelfCorrectingLenses

instance Arbitrary Err where
  arbitrary = oneof [ExitCode <$> arbitrary, ReallyBadError <$> arbitrary]

instance Arbitrary Prenu where
  arbitrary = Prenu <$> arbitrary <*> arbitrary

instance Arbitrary Builder where
  arbitrary = Builder <$> arbitrary <*> arbitrary

exercise_Laws :: Spec
exercise_Laws = do
  it "1.1 get-set law should fail" $ expectFailure $
    \s -> set unlawful2 (view unlawful2 s) s == s
  it "1.2 set-set law should fail" $ expectFailure $
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


  it "4 prenu doesn't satisfy all lens rules but is still useful" $
        -- breaks get-set law
        expectFailure (\s -> set prenuNilciho (view prenuNilciho s) s == s)
        -- satisfies set-set law
    .&. property (\b s -> set prenuNilciho b (set prenuNilciho b s) ==
                          set prenuNilciho b s)
        -- breaks set-get law
    .&. expectFailure (\b s -> view prenuNilciho (set prenuNilciho b s) == b)

  it "5 break all laws" $
        expectFailure (\s -> set breakAllLaws (view breakAllLaws s) s == s)
    .&. expectFailure (\b s -> set breakAllLaws b (set breakAllLaws b s) ==
                               set breakAllLaws b s)
    .&. expectFailure (\b s -> view breakAllLaws (set breakAllLaws b s) == b)

  it "6 lawful builder lens" $ isLens builderLens

exercise_VirtualFields :: Spec
exercise_VirtualFields = do
  let user = User "John" "Cena" "invisible@example.com"
  it "2.1 fullName lens: view works" $
    view fullName user `shouldBe` "John Cena"
  it "2.1 fullName lens: set works" $
    set fullName "Doctor of Thuganomics" user `shouldBe`
    User { _firstName = "Doctor"
         , _lastName = "of Thuganomics"
         , _email = "invisible@example.com"
         }

exercise_SelfCorrectingLenses :: Spec
exercise_SelfCorrectingLenses = do
  let prices = ProducePrices 1.50 1.48
  it "test 1" $
    set limePrice' 2 prices `shouldBe` ProducePrices 2.0 1.5
  it "test 2" $
    set limePrice' 1.8 prices `shouldBe` ProducePrices 1.8 1.48
  it "test 3" $
    set limePrice' 1.63 prices `shouldBe` ProducePrices 1.63 1.48
  it "test 4" $
    set limePrice' (-1.0) prices `shouldBe` ProducePrices 0.0 0.5
