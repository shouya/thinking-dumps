{-# LANGUAGE PartialTypeSignatures #-}

{- HLINT ignore "Use camelCase" -}
{- HLINT ignore "Redundant $" -}
{- HLINT ignore "Redundant do" -}
module ExerciseSpec (spec) where

-- import qualified Data.Text as T

import Control.Applicative
import Control.Exception (evaluate)
import Control.Lens hiding ((&))
import Control.Lens.Properties
import Control.Monad.State
import Data.Char (isAlpha, isUpper, toLower, toUpper)
import Data.Function hiding ((&))
import Data.List (transpose)
import qualified Data.Map as M
import Data.Monoid
import Data.Ord
import qualified Data.Set as S
import Exercise
import Numeric.Lens
import Test.Hspec
import Test.QuickCheck

spec :: Spec
spec = do
  exercise_Laws
  exercise_VirtualFields
  exercise_SelfCorrectingLenses
  exercise_PolymorphicLenses
  exercise_LensCompositions
  exercise_Operators
  exercise_SimpleFolds
  exercise_CustomFolds
  exercise_FoldActions
  exercise_HigherOrderFolds
  exercise_Filtering
  exercise_SimpleTraversals
  exercise_TraversalActions
  exercise_CustomTraversals
  exercise_TraversalLaws
  exercise_PartsOf
  exercise_IndexableStructures
  exercise_CustomIndexedStructures
  exercise_MissingValues
  exercise_Prisms
  exercise_CustomPrisms
  exercise_PrismLaws
  exercise_IntroToIsos
  exercise_ProjectedIsos

-- redefine (&) to infixl 2 (was infixl 1 in Control.Lens).
-- so it plays well with `shouldBe`
infixl 2 &

(&) :: a -> (a -> b) -> b
a & f = f a

instance Arbitrary Err where
  arbitrary = oneof [ExitCode <$> arbitrary, ReallyBadError <$> arbitrary]

instance Arbitrary Prenu where
  arbitrary = Prenu <$> arbitrary <*> arbitrary

instance Arbitrary Builder where
  arbitrary = Builder <$> arbitrary <*> arbitrary

exercise_Laws :: Spec
exercise_Laws = do
  it "1.1 get-set law should fail" $
    expectFailure $
      \s -> set unlawful2 (view unlawful2 s) s == s
  it "1.2 set-set law should fail" $
    expectFailure $
      \b s -> set unlawful3 b (set unlawful3 b s) == set unlawful3 b s

  -- cheating with quick check
  it "2.1 test get-set law for msg" $
    property $
      \s -> set msg (view msg s) s == s
  it "2.2 test set-set law for msg" $
    expectFailure $
      \b s -> set msg b (set msg b s) == s

  it "3.1 test set-set law for msg" $
    property $
      \b s -> set msg' b (set msg' b s) == set msg' b s
  it "3.2 test set-get law for msg" $
    property $
      \b s -> view msg' (set msg' b s) == b
  it "3.3 test get-set law for msg" $
    expectFailure $
      \s -> set msg' (view msg' s) s == s

  it "4 prenu doesn't satisfy all lens rules but is still useful" $
    -- breaks get-set law
    expectFailure (\s -> set prenuNilciho (view prenuNilciho s) s == s)
      -- satisfies set-set law
      .&. property
        ( \b s ->
            set prenuNilciho b (set prenuNilciho b s)
              == set prenuNilciho b s
        )
      -- breaks set-get law
      .&. expectFailure (\b s -> view prenuNilciho (set prenuNilciho b s) == b)

  it "5 break all laws" $
    expectFailure (\s -> set breakAllLaws (view breakAllLaws s) s == s)
      .&. expectFailure
        ( \b s ->
            set breakAllLaws b (set breakAllLaws b s)
              == set breakAllLaws b s
        )
      .&. expectFailure (\b s -> view breakAllLaws (set breakAllLaws b s) == b)

  it "6 lawful builder lens" $ isLens builderLens

exercise_VirtualFields :: Spec
exercise_VirtualFields = do
  let user = User "John" "Cena" "invisible@example.com"
  it "2.1 fullName lens: view works" $
    view fullName user `shouldBe` "John Cena"
  it "2.1 fullName lens: set works" $
    set fullName "Doctor of Thuganomics" user
      `shouldBe` User
        { _firstName = "Doctor",
          _lastName = "of Thuganomics",
          _email = "invisible@example.com"
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

instance Arbitrary a => Arbitrary (Preferences a) where
  arbitrary = Preferences <$> arbitrary <*> arbitrary

instance Eq a => Eq (Preferences a) where
  Preferences a b == Preferences a' b' = a == a' && b == b'

exercise_PolymorphicLenses :: Spec
exercise_PolymorphicLenses = do
  it "1. write down type type signature" $ do
    -- type Lens (Volpal x) (Volpal y) x y =
    --     forall f. Functor f => (x -> f y) -> Vorpal x -> f (Vorpal y)
    True

  -- I commented this out because my document formatter doesn't play well
  -- with the @Type application syntax.
  --
  -- it "2. change the type of the best and worst fields" $
  --   -- polymorphic lens laws do not type check, so I'll only test for
  --   -- the cases when a ~ b.
  --   isLens (preferenceLens @String @String)
  --   .&.
  --   isLens (preferenceLens @Int @Int)

  it "3. What is the type of the lens" $
    -- type Lens (Result a) (Result b) (Either a String) (Either b String) =
    -- the focus cannot be a and b because lens require us to focus on a single
    -- focus, while Either don't always give us an a or b.
    True

  it "4. Is it possible to change more than one type variable at a time?" $
    -- Yes! Lens (Foo s s') (Foo t t') (s, s') (t, t') is valid
    True

  it "5. write a lens for (Predicate a)" $
    -- It's impossible to get an 'a' from Predicate a. We can get
    -- a (a -> Bool) function though.
    True

exercise_LensCompositions :: Spec
exercise_LensCompositions = do
  it "1. fill in the blank" $
    view (_2 . _1 . _2) ("Ginerva", (("Galileo", "Waldo"), "Malfoy"))
      `shouldBe` "Waldo"

  it "2. fill in the missing type" $
    -- mysteryDomino :: Eight Two
    True

  it "3. rewrite the type as polymoprhic lens" $
    -- Functor f => (Armadillo -> f Hedgehog) -> (Platypus -> f BabySloth)
    -- Lens Platypus BabySloth Armadillo Hedgehog
    True

  it "4. Find a way to compose ALL of the following lensees" $
    -- trivial
    True

exercise_Operators :: Spec
exercise_Operators = do
  it "1.1 reach goal A" $ do
    let goalA = Kingdom {_name = "Duloc: a perfect place", _army = Army {_archers = 22, _knights = 42}, _gate = Gate {_open = False, _oilTemp = 10.0}}
    let goalA' =
          duloc & name <>~ ": a perfect place"
            & army . knights .~ 42
            & gate . open %~ not
    goalA' `shouldBe` goalA

  it "1.2 reach goal B" $ do
    let goalB = Kingdom {_name = "Dulocinstein", _army = Army {_archers = 17, _knights = 26}, _gate = Gate {_open = True, _oilTemp = 100.0}}
    let goalB' =
          duloc & name .~ "Dulocinstein"
            & army . archers -~ 5
            & army . knights *~ 2
            & army . knights -~ 2
            & gate . oilTemp ^~ 2
    goalB' `shouldBe` goalB

  it "1.3 reach goal C" $ do
    let goalC = ("Duloc: Home", Kingdom {_name = "Duloc: Home of the talking Donkeys", _army = Army {_archers = 22, _knights = 14}, _gate = Gate {_open = True, _oilTemp = 5.0}})
    let goalC' =
          duloc & name .~ "Duloc: Home"
            & gate . oilTemp -~ 5
            & name <<<>~ " of the talking Donkeys"
    goalC' `shouldBe` goalC

  it "2.1 fill in undefined" $ do
    let goal = (True, "opossums")
    let goal' = (False, "opossums") & _1 ||~ True
    goal' `shouldBe` goal

  it "2.2 fill in undefined" $ do
    let goal = ((False, "DUDLEY - THE WORST"), 20.0)
    let goal' =
          ((True, "Dudley"), 55.0) & _1 . _2 <>~ " - the worst"
            & _2 -~ 15
            & _2 //~ 2
            & _1 . _2 %~ map toUpper
            & _1 . _1 &&~ False
    goal' `shouldBe` goal

  it "3. Name a lens operator that takes only two arguments" $ do
    -- (^.)
    True

  it "4. What’s the type signature of %∼?" $ do
    -- (%~) :: Lens s t a b -> (a -> b) -> s -> t
    True

exercise_SimpleFolds :: Spec
exercise_SimpleFolds = do
  it "1. guess the results" $ do
    let beastSizes = [(3, "Sirens"), (882, "Kraken"), (92, "Ogopogo")]
    beastSizes ^.. folded `shouldBe` [(3, "Sirens"), (882, "Kraken"), (92, "Ogopogo")]
    beastSizes ^.. folded . folded `shouldBe` ["Sirens", "Kraken", "Ogopogo"]
    beastSizes ^.. folded . folded . folded `shouldBe` "SirensKrakenOgopogo"
    beastSizes ^.. folded . _2 `shouldBe` beastSizes ^.. folded . folded
    toListOf (folded . folded) [[1, 2, 3], [4, 5, 6]] `shouldBe` [1, 2, 3, 4, 5, 6]
    toListOf (folded . folded) (M.fromList [("Jack", "Captain"), ("Will", "First Mate")])
      `shouldBe` "CaptainFirst Mate"
    ("Hello", "It's me") ^.. both . folded `shouldBe` "HelloIt's me"
    ("Why", "So", "Serious?") ^.. each `shouldBe` ["Why", "So", "Serious?"]
    let quotes = [("Why", "So", "Serious?"), ("This", "is", "SPARTA")]
    quotes ^.. each . each . each `shouldBe` "WhySoSerious?ThisisSPARTA"

  it "2. Write out the 'specialized' types" $ do
    -- toListOf (folded . _1) [(1, 'a'), (2, 'b'), (3, 'c')]
    -- folded :: Fold [(Int, Char)] (Int, Char)
    -- _1     :: Fold (Int, Char) Char

    -- toListOf (_2 . folded) (False, S.fromList ["one", "two", "three"])
    -- _2       :: Fold (Bool, Set String) (Set String)
    -- folded   :: Fold (Set String) String
    -- toListOf :: Fold (Bool, Set String) String -> (Bool, Set String) -> [String]

    -- toListOf (folded . folded) (M.fromList [("Jack", "Captain"), ("Will", "First Mate")])
    -- folded (1st) :: Fold (Map String String) String
    -- folded (2nd) :: Fold String Char
    -- toListOf     :: Fold (Map String String) Char -> Map String String -> [Char]
    True

  it "3. Fill in the blank" $ do
    [1, 2, 3] ^.. folded `shouldBe` [1, 2, 3]
    [1, 2, 3] ^.. id `shouldBe` [[1, 2, 3]]
    ("Light", "Dark") ^.. _1 `shouldBe` ["Light"]
    [("Light", "Dark"), ("Happy", "Sad")] ^.. folded . both
      `shouldBe` ["Light", "Dark", "Happy", "Sad"]
    [("Light", "Dark"), ("Happy", "Sad")] ^.. folded . _1
      `shouldBe` ["Light", "Happy"]
    [("Light", "Dark"), ("Happy", "Sad")] ^.. folded . _2 . folded
      `shouldBe` "DarkSad"
    ("Bond", "James", "Bond") ^.. each
      `shouldBe` ["Bond", "James", "Bond"]

exercise_CustomFolds :: Spec
exercise_CustomFolds = do
  it "1. fill in the blanks" $ do
    ["Yer", "a", "wizard", "Harry"] ^.. folded . folded
      `shouldBe` "YerawizardHarry"
    [[1, 2, 3], [4, 5, 6]] ^.. folded . folding (take 2)
      `shouldBe` [1, 2, 4, 5]
    [[1, 2, 3], [4, 5, 6]] ^.. folded . to (take 2)
      `shouldBe` [[1, 2], [4, 5]]
    ["bob", "otto", "hannah"] ^.. folded . to reverse
      `shouldBe` ["bob", "otto", "hannah"]
    ("abc", "def") ^.. folding (\(a, b) -> [a, b]) . to reverse . folded
      `shouldBe` "cbafed"

  it "2. fill in the blanks" $ do
    [1 .. 5] ^.. folded . to (* 100)
      `shouldBe` [100, 200, 300, 400, 500]

    (1, 2) ^.. both
      `shouldBe` [1, 2]

    [(1, "one"), (2, "two")] ^.. folded . _2
      `shouldBe` ["one", "two"]

    (Just 1, Just 2, Just 3) ^.. each . folded
      `shouldBe` [1, 2, 3]

    [Left 1, Right 2, Left 3] ^.. folded . folded
      `shouldBe` [2]

    [([1, 2], [3, 4]), ([5, 6], [7, 8])] ^.. folded . both . folded
      `shouldBe` [1, 2, 3, 4, 5, 6, 7, 8]

    [1, 2, 3, 4]
      ^.. folding (\[a, b, c, d] -> [(a, b), (c, d)])
        . folding (\(a, b) -> [Left a, Right b])
      `shouldBe` [Left 1, Right 2, Left 3, Right 4]

    [(1, (2, 3)), (4, (5, 6))] ^.. folded . folding (\(a, (b, c)) -> [a, b, c])
      `shouldBe` [1, 2, 3, 4, 5, 6]

    [(Just 1, Left "one"), (Nothing, Right 2)]
      ^.. folded
        . folding (\(a, b) -> [a ^.. folded, b ^.. folded])
        . folded
      `shouldBe` [1, 2]

    [(1, "one"), (2, "two")] ^.. folded . folding (\(a, b) -> [Left a, Right b])
      `shouldBe` [Left 1, Right "one", Left 2, Right "two"]
    S.fromList ["apricots", "apples"] ^.. folded . folding reverse
      `shouldBe` "selppastocirpa"

  it "3. (bonus) Devise a fold which returns the expected results." $ do
    [(12, 45, 66), (91, 123, 87)] ^.. folded . _2 . folding (reverse . show)
      `shouldBe` "54321"

    [(1, "a"), (2, "b"), (3, "c"), (4, "d")]
      ^.. folded . folding (\(a, b) -> if even a then Just b else Nothing)
      `shouldBe` ["b", "d"]

exercise_FoldActions :: Spec
exercise_FoldActions = do
  it "1. Pick the matching action from the list" $ do
    has folded [] `shouldBe` False
    foldOf both ("Yo", "Adrian!") `shouldBe` "YoAdrian!"
    elemOf each "phone" ("E.T.", "phone", "home")
      `shouldBe` True
    minimumOf folded [5, 7, 2, 3, 13, 17, 11]
      `shouldBe` Just 2
    lastOf folded [5, 7, 2, 3, 13, 17, 11]
      `shouldBe` Just 11
    anyOf folded ((> 9) . length) ["Bulbasaur", "Charmander", "Squirtle"]
      `shouldBe` True
    findOf folded even [11, 22, 3, 5, 6]
      `shouldBe` Just 22

  it "2. retrieve the output from the input" $ do
    let input1 = ["umbrella", "olives", "racecar", "hammer"]
    let output1 = Just "racecar"
    findOf folded (\x -> x == reverse x) input1 `shouldBe` output1

    let input2 = (2, 4, 6)
    let output2 = True
    allOf each even input2 `shouldBe` output2

    let input3 = [(2, "I'll"), (3, "Be"), (1, "Back")]
    let output3 = Just (3, "Be")
    maximumByOf each (comparing fst) input3 `shouldBe` output3

    let input4 = (1, 2)
    let output4 = 3
    getSum (foldMapOf both Sum input4) `shouldBe` output4

  it "3. bonus" $ do
    let input1 = "Do or do not, there is no try."
    let output1 = Just "there"
    maximumByOf worded (comparing (length . filter (`elem` "aeiou"))) input1
      `shouldBe` output1

    let input2 = ["a", "b", "c"]
    let output2 = "cba"
    foldOf (reversed . folded) input2
      `shouldBe` output2

    let input3 = [(12, 45, 66), (91, 123, 87)]
    let output3 = "54321"
    foldOf (folded . _2 . to show . reversed) input3
      `shouldBe` output3

    let input4 = [(1, "a"), (2, "b"), (3, "c"), (4, "d")]
    let output4 = ["b", "d"]
    input4 ^.. folded . filtered (even . fst) . _2
      `shouldBe` output4

exercise_HigherOrderFolds :: Spec
exercise_HigherOrderFolds = do
  it "1. fill in the blanks" $ do
    "Here's looking at you, kid" ^.. dropping 7 folded
      `shouldBe` "looking at you, kid"

    ["My Precious", "Hakuna Matata", "No problemo"] ^.. folded . taking 1 worded
      `shouldBe` ["My", "Hakuna", "No"]

    ["My Precious", "Hakuna Matata", "No problemo"] ^.. taking 1 (folded . worded)
      `shouldBe` ["My"]

    ["My Precious", "Hakuna Matata", "No problemo"] ^.. folded . taking 1 worded . folded
      `shouldBe` "MyHakunaNo"

    ["My Precious", "Hakuna Matata", "No problemo"] ^.. folded . takingWhile isAlpha folded
      `shouldBe` "MyHakunaNo"

    sumOf (taking 2 each) (10, 50, 100)
      `shouldBe` 60

    ("stressed", "guns", "evil") ^.. backwards each
      `shouldBe` ["evil", "guns", "stressed"]

    ("stressed", "guns", "evil") ^.. backwards each . to reverse
      `shouldBe` ["live", "snug", "desserts"]

    "blink182 k9 blazeit420" ^.. worded . droppingWhile isAlpha folded
      `shouldBe` "1829420"

  describe "2. solve the problems" $ do
    let sample = [-10, -5, 4, 3, 8, 6, -2, 3, -5, -7] :: [Int]

    it "find # of days it took to thaw" $ do
      lengthOf (takingWhile (< 0) folded) sample `shouldBe` 2

    it "warmest temperature in first 4 days" $ do
      maximumOf (taking 4 each) sample `shouldBe` Just 4

    it "the temperature after the warmest day in the 4 days" $ do
      let maxTemp = 4
      sample ^? dropping 1 (droppingWhile (/= maxTemp) each) `shouldBe` Just 3

    it "how many freezing days at the end" $ do
      lengthOf (takingWhile (< 0) (reversed . each)) sample `shouldBe` 2

    it "list the days from first thaw to next freeze" $ do
      sample ^.. takingWhile (>= 0) (droppingWhile (< 0) each)
        `shouldBe` [4, 3, 8, 6]

    it "bonus: list the days from first thaw to last freeze" $ do
      sample ^.. backwards (droppingWhile (< 0) $ backwards $ droppingWhile (< 0) each)
        `shouldBe` [4, 3, 8, 6, -2, 3]

      let trimmingWhile p = backwards . droppingWhile p . backwards . droppingWhile p
      sample ^.. trimmingWhile (< 0) each
        `shouldBe` [4, 3, 8, 6, -2, 3]

exercise_Filtering :: Spec
exercise_Filtering = do
  it "list all cards whose name starts with 'S'" $ do
    let cards = deck ^.. folded . filteredBy (cardName . _head . only 'S')
    let cards' = filter (\c -> head (_cardName c) == 'S') deck
    cards `shouldBe` cards'

  it "find lowest attack power of all moves" $ do
    let card = minimumByOf (folded . moves . folded) (compare `on` _movePower) deck
    card `shouldBe` Just (Move "Soggy" 3)

  it "find the name of first card with more than one move" $ do
    let card =
          deck
            ^? folded
              . filteredBy (moves . to length . filtered (> 1))
              . cardName
    card `shouldBe` Just "Kapichu"

  it "find any Hot cards with a move with more than 30 power" $ do
    let card =
          deck
            ^? folded
              . filteredBy (aura . only Hot)
              . filteredBy (moves . folded . movePower . filtered (> 30))
              . cardName
    card `shouldBe` Just "Spicyeon"

  it "list all names of holographic cards with a Wet aura" $ do
    let cards =
          deck
            ^.. folded
              . filteredBy (aura . only Wet)
              . filteredBy (holo . only True)
              . cardName
    cards `shouldBe` ["Garydose"]

  it "find sum of all attack power belonging to non-leafy cards" $ do
    let power =
          flip sumOf deck $
            folded
              . filteredBy (aura . filtered (/= Leafy))
              . moves
              . folded
              . movePower
    power `shouldBe` 303

exercise_SimpleTraversals :: Spec
exercise_SimpleTraversals = do
  describe "short questions" $ do
    it "What type of optic: compose a traversal with a fold?" $ do
      -- Fold
      True
    it "Which of the optics we’ve learned can act as a traversal?" $ do
      -- Lens, Traversal
      True
    it "Which of the optics we’ve learned can act as a fold?" $ do
      -- Lens, Fold, Traversal
      True

  describe "fill the blanks" $ do
    it "1" $ do
      (("Jurassic", "Park") & each .~ "N/A") `shouldBe` ("N/A", "N/A")
    it "2" $ do
      (("Jurassic", "Park") & both . traversed .~ 'x')
        `shouldBe` ("xxxxxxxx", "xxxx")
    it "3" $ do
      (("Malcolm", ["Kaylee", "Inara", "Jayne"]) & beside id traversed %~ take 3)
        `shouldBe` ("Mal", ["Kay", "Ina", "Jay"])
    it "4" $ do
      (("Malcolm", ["Kaylee", "Inara", "Jayne"]) & _2 . element 1 .~ "River")
        `shouldBe` ("Malcolm", ["Kaylee", "River", "Jayne"])
    it "5" $ do
      let result =
            ["Die Another Day", "Live and Let Die", "You Only Live Twice"]
              & traversed . elementOf worded 1 . traversed .~ 'x'
      result
        `shouldBe` [ "Die xxxxxxx Day",
                     "Live xxx Let Die",
                     "You xxxx Live Twice"
                   ]
    it "6" $ do
      let result = ((1, 2), (3, 4)) & beside both both +~ 1
      result `shouldBe` ((2, 3), (4, 5))

    it "7" $ do
      let result = (1, (2, [3, 4])) & beside id (beside id each) +~ 1
      result `shouldBe` (2, (3, [4, 5]))

    it "8" $ do
      let result =
            ((True, "Strawberries"), (False, "Blueberries"), (True, "Blackberries"))
              & each . filtered fst . _2 . taking 5 traversed %~ toUpper
      result
        `shouldBe` ((True, "STRAWberries"), (False, "Blueberries"), (True, "BLACKberries"))

    it "9" $ do
      let input = ((True, "Strawberries"), (False, "Blueberries"), (True, "Blackberries"))
      let result = input & each %~ snd
      result `shouldBe` ("Strawberries", "Blueberries", "Blackberries")

exercise_TraversalActions :: Spec
exercise_TraversalActions = do
  describe "fill in the blanks" $ do
    it "1" $ do
      sequenceAOf _1 (Nothing :: Maybe Int, "Rosebud") `shouldBe` Nothing
    it "2" $ do
      let result = [[('a', 1), ('c', 2)], [('a', 1), ('d', 2)], [('b', 1), ('c', 2)], [('b', 1), ('d', 2)]]
      let input = [("ab", 1), ("cd", 2)]
      sequenceAOf (traversed . _1) input `shouldBe` result
    it "3" $ do
      let result = sequenceAOf traversed [ZipList [1, 2], ZipList [3, 4]]
      result `shouldBe` ZipList [[1, 3], [2, 4]]
    it "4" $ do
      let result = sequenceAOf (traversed . _2) [('a', ZipList [1, 2]), ('b', ZipList [3, 4])]
      result `shouldBe` ZipList [[('a', 1), ('b', 3)], [('a', 2), ('b', 4)]]
    it "5" $ do
      let input = ([1, 1, 1], (1, 1))
      let traversal = beside each both
      let result = traverseOf traversal (\n -> modify (+ n) >> get) input
      runState result 0 `shouldBe` (([1, 2, 3], (4, 5)), 5)

  describe "run the following with %%~" $ do
    it "1" $ do
      let result = ("ab", True) & (_1 . traversed) %%~ (\c -> [toLower c, toUpper c])
      result `shouldBe` [("ab", True), ("aB", True), ("Ab", True), ("AB", True)]
    it "2" $ do
      let input = [('a', True), ('b', False)]
      let expect = input & (traversed . _1) %%~ (\c -> [toLower c, toUpper c])
      let result = [[('a', True), ('b', False)], [('a', True), ('B', False)], [('A', True), ('b', False)], [('A', True), ('B', False)]]
      expect `shouldBe` result

  describe "write a validation function" $ do
    let validateAge account = account & user . age %%~ validate
          where
            validate age
              | age <= 0 = Left "Age must be greater than 0"
              | age >= 150 = Left "Age must be less than 150"
              | otherwise = Right age
    let badAccount1 = Account "bad1" (UserT "bad1" (-10))
    let badAccount2 = Account "bad2" (UserT "bad2" 170)
    let goodAccount = Account "good" (UserT "good" 25)
    it "invalid age case 1" $ do
      has _Left (validateAge badAccount1)
    it "invalid age case 2" $ do
      has _Left (validateAge badAccount2)
    it "valid age case" $ do
      validateAge goodAccount `shouldBe` Right goodAccount

exercise_CustomTraversals :: Spec
exercise_CustomTraversals = do
  let transactions = [Deposit 10, Withdrawal 20, Deposit 30]
  it "1. rewrite amount transaction" $ do
    let transactions' = transactions & traversed . amountT %~ (+ 1)
    transactions' `shouldBe` [Deposit 11, Withdrawal 21, Deposit 31]

  it "2. rewrite both" $ do
    (1, 2) & bothT %~ (* 5) `shouldBe` (5, 10)

  it "3. rewrite transaction delta" $ do
    Deposit 10 ^? transactionDelta `shouldBe` Just 10
    Withdrawal 10 ^? transactionDelta `shouldBe` Just (-10)
    Deposit 10 & transactionDelta .~ 15 `shouldBe` Deposit 15
    Withdrawal 10 & transactionDelta .~ (-15) `shouldBe` Withdrawal 15
    Deposit 10 & transactionDelta +~ 5 `shouldBe` Deposit 15
    Withdrawal 10 & transactionDelta +~ 5 `shouldBe` Withdrawal 5

  it "4. implement left" $ do
    Left 5 & leftT +~ 5 `shouldBe` (Left 10 :: Either Int Int)
    Right 5 & leftT +~ 5 `shouldBe` (Right 5 :: Either Int Int)
    Left 5 & leftT .~ 10 `shouldBe` (Left 10 :: Either Int Int)
    Right 5 & leftT +~ 10 `shouldBe` (Right 5 :: Either Int Int)

  it "5. Bonus: Reimplement beside" $
    ((1, 2), 3) & besideT both id +~ 3 `shouldBe` ((4, 5), 6)

exercise_TraversalLaws :: Spec
exercise_TraversalLaws = do
  it "1. which law does worded break?" $ do
    -- it breaks the "coherent focus" law.
    "foo bar" & worded <>~ " baz" & worded <>~ "a" `shouldBe` "fooa baza bara baza"
    "foo bar" & worded <>~ "a baz" `shouldBe` "fooa baz bara baz"

  it "2. break the first law!" $ do
    5 & law1BreakingT %%~ pure `shouldNotBe` (pure 5 :: [Int])

  it "3. break the second law!" $ do
    2 & law2BreakingT %~ (`div` 2) & law2BreakingT %~ (+ 1)
      `shouldNotBe` 2 & law2BreakingT %~ ((+ 1) . (`div` 2))
    2 & filtered even %~ (`div` 2) & filtered even %~ (+ 1)
      `shouldNotBe` 2 & filtered even %~ ((+ 1) . (`div` 2))

  describe "4. decide if the these traversal are lawful or not" $ do
    it "taking" $ do
      -- taking is lawful. for law 2, the focused elements are fixed
      True

    it "beside" $ do
      -- beside is lawful. for law 2, the focus is fixed
      True

    it "each" $ do
      --- lawful. the focus is fixed.
      True

    it "lined" $
      do
        -- not lawful. same reason as worded
        "foo\nbar" & lined <>~ "\nbaz" & lined <>~ "X"
        `shouldNotBe` "foo\nbar" & lined <>~ "X\nbaz"

    it "traversed" $ do
      -- lawful
      True

exercise_PartsOf :: Spec
exercise_PartsOf = do
  it "fill in the blanks" $ do
    [1, 2, 3, 4] ^. partsOf (traversed . filtered even)
      `shouldBe` [2, 4]

    ["Aardvark", "Bandicoot", "Capybara"]
      -- the original book uses "^." which doesn't type check
      ^.. traversed . partsOf (taking 3 traversed)
      `shouldBe` ["Aar", "Ban", "Cap"]

    ([1, 2], M.fromList [('a', 3), ('b', 4)])
      ^. partsOf (beside each each)
      `shouldBe` [1, 2, 3, 4]

    [1, 2, 3, 4] & partsOf (traversed . filtered even) .~ [20, 40]
      `shouldBe` [1, 20, 3, 40]

    ["Aardvark", "Bandicoot", "Capybara"]
      & partsOf (taking 1 traversed . traversed) .~ "Kangaroo"
      `shouldBe` ["Kangaroo", "Bandicoot", "Capybara"]

    ["Aardvark", "Bandicoot", "Capybara"]
      & partsOf (traversed . traversed) .~ "Ant"
      --- the original book missed a blank
      `shouldBe` ["Antdvark", "Bandicoot", "Capybara"]
  it "try out my handcrafted partsOf combinator" $ do
    [1, 2, 3, 4] & myPartsOf (traversed . filtered even) %~ reverse
      `shouldBe` [1, 4, 3, 2]

    [1, 2, 3, 4] & myUnsafePartsOf traversed %~ map show
      `shouldBe` ["1", "2", "3", "4"]

-- the rest of the problems don't have answerable blanks

exercise_IndexableStructures :: Spec
exercise_IndexableStructures = do
  it "1. fill in the blanks" $ do
    ["Larry", "Curly", "Moe"]
      & ix 1 .~ "Wiggly"
      `shouldBe` ["Larry", "Wiggly", "Moe"]

    let heroesAndVillains = M.fromList [("Superman", "Lex"), ("Batman", "Joker")]

    heroesAndVillains & at "Spiderman" ?~ "Goblin"
      `shouldBe` M.fromList [("Batman", "Joker"), ("Spiderman", "Goblin"), ("Superman", "Lex")]

    sans "Superman" heroesAndVillains
      `shouldBe` M.fromList [("Batman", "Joker")]

    S.fromList ['a', 'e', 'i', 'o', 'u']
      & at 'y' ?~ ()
      & at 'i' .~ Nothing
      `shouldBe` S.fromList "aeouy"

  it "2. use ix and at to go from input to the output" $ do
    let input = M.fromList [("candy bars", 13), ("soda", 34), ("gum", 7)]
    let output = M.fromList [("candy bars", 13), ("ice cream", 5), ("soda", 37)]

    input
      & ix "soda" .~ 37
      & sans "gum"
      & at "ice cream" ?~ 5
      `shouldBe` output

exercise_CustomIndexedStructures :: Spec
exercise_CustomIndexedStructures = do
  -- Implement both Ixed and At for a newtype wrapper around a Map
  -- which makes indexing case insensitive, you can specialize to
  -- String or Text keys. Write the ix instance manually even though
  -- it has a default implementation. It’s okay to assume that user
  -- will only interact with the map via Ixed and At.
  let m = CIMap (M.fromList [("happy", 10 :: Int)])
  it "ix works" $ do
    m & ix "Happy" .~ 12 `shouldBe` CIMap (M.fromList [("happy", 12)])

exercise_MissingValues :: Spec
exercise_MissingValues = do
  it "1. focus the value at key 'first' or 'second" $ do
    let optic = ix "first" `failing` ix "second"
    M.fromList [("first", False), ("second", False)] & optic .~ True
      `shouldBe` M.fromList [("first", True), ("second", False)]

    M.fromList [("second", False)] & optic .~ True
      `shouldBe` M.fromList [("second", True)]

  it "2. focus first element if it's even, otherwise focus the second" $ do
    let optic = (ix 0 . filtered even) `failing` (ix 1 . filtered odd)
    (1, 1) & optic *~ 10 `shouldBe` (1, 10)
    (2, 2) & optic *~ 10 `shouldBe` (20, 2)

  it "3. focus all even numbers in a list, if none then focus all numbers" $ do
    let optic = (traversed . filtered even) `failing` traversed
    [1, 2, 3, 4] ^.. optic `shouldBe` [2, 4]
    [1, 3, 5] ^.. optic `shouldBe` [1, 3, 5]

  it "4. fill the blanks" $ do
    Nothing ^. non "default" `shouldBe` "default"
    Nothing & non 100 +~ 7 `shouldBe` Just 107

    M.fromList [("Perogies", True), ("Pizza", True), ("Pilsners", True)]
      ^. at "Broccoli" . non False `shouldBe` False

    M.fromList [("Breath of the wild", 22000000), ("Odyssey", 9070000)]
      & at "Wario's Woods" . non 0 +~ 999
      `shouldBe` M.fromList
        [ ("Breath of the wild", 22000000),
          ("Odyssey", 9070000),
          ("Wario's Woods", 999)
        ]

    ["Math", "Science", "Geograph"] ^. pre (ix 10) . non "Unscheduled"
      `shouldBe` "Unscheduled"

  it "bonus" $ do
    [1, 2, 3, 4] ^.. traversed . pre (filtered even) . non (-1)
      `shouldBe` [-1, 2, -1, 4]

exercise_Prisms :: Spec
exercise_Prisms = do
  it "1. what prisms will be generated?" $ do
    -- _Email :: Prism' ContactInfo String
    -- _Telephone :: Prism' ContactInfo Int
    -- _Address :: Prism' (String, String, String)
    True

  it "2. Fill in the blanks" $ do
    (Right 35 & _Right +~ 5) `shouldBe` (Right 40 :: _ () _)

    [Just "Mind", Just "Power", Nothing, Just "Soul", Nothing, Just "Time"]
      ^.. folded . _Just `shouldBe` ["Mind", "Power", "Soul", "Time"]

    [Just "Mind", Just "Power", Nothing, Just "Soul", Nothing, Just "Time"]
      & traversed . _Just <>~ " Stone"
      `shouldBe` [ Just "Mind Stone",
                   Just "Power Stone",
                   Nothing,
                   Just "Soul Stone",
                   Nothing,
                   Just "Time Stone"
                 ]

    Left (Right True, "Eureka!") & _Left . _1 . _Right %~ not
      `shouldBe` (Left (Right False :: _ () _, "Eureka!") :: _ _ ())

    _Cons # ("Do", ["Re", "Mi"]) `shouldBe` ["Do", "Re", "Mi"]

    isn't (_Show :: Prism' String Int) "not an int" `shouldBe` True

  it "3.1 convert input to output" $ do
    let input = (Just 1, Nothing, Just 3)
    let output = [1, 3]
    input ^.. each . _Just `shouldBe` output

  it "3.2 convert input to output" $ do
    let input = ('x', "yz")
    let output = "xzy"
    _Cons # (input & _2 %~ reverse) `shouldBe` output

  it "3.3 convert input to output" $ do
    let input = "do the hokey pokey"
    let output = Left (Just (Right "do the hokey pokey"))
    -- stupid! gotta specify all unknown types
    _Left . _Just . _Right # input `shouldBe` (output :: _ (_ (_ () _)) ())

exercise_CustomPrisms :: Spec
exercise_CustomPrisms = do
  it "1. write a _Tail prism" $ do
    -- It's not possible. Because there is no lawful implementation of "embed".
    True

  it "2. write a _ListCons prism" $ do
    -- See Exercise.hs
    True
  it "3. (Bonus) Implement _Cycle to detect exactly 'n' repetitions" $ do
    "dogdogdog" ^? _Cycles 3 `shouldBe` Just "dog"
    "dogdogdogdog" ^? _Cycles 3 `shouldBe` Nothing
    "aaa" ^? _Cycles 3 `shouldBe` Just "a"
    "xyz" ^? _Cycles 3 `shouldBe` Nothing
    _Cycles 3 # "dog" `shouldBe` "dogdogdog"
    "dogdogdog" & _Cycles 3 .~ "cats" `shouldBe` "catscatscats"

exercise_PrismLaws :: Spec
exercise_PrismLaws = do
  it "1. implement _Contains prism and determine if it's lawful" $ do
    -- It is not lawful. It breaks the review-preview law.
    _Contains 1 # S.fromList [1] & preview (_Contains 1)
      `shouldNotBe` Just (S.fromList [1])
    _Contains 1 # S.fromList [1] & preview (_Contains 1)
      `shouldBe` Just (S.fromList [])

  it "2. is _Singleton lawful?" $ do
    -- it is
    let law1 a = preview _Singleton (review _Singleton a) == Just (a :: Int)
        law2 s = case preview _Singleton s of
          Nothing -> True
          Just (a :: Int) -> review _Singleton a == s
        law3 s = case matching _Singleton (s :: [Int]) of
          Left (t :: [Int]) -> matching _Singleton t == Left s
          Right _ -> True
     in property law1 .&. property law2 .&. property law3

  it "3. write a Prism that fails the first law" $ do
    _PlusOne # (-1) & review _PlusOne `shouldNotBe` (-1)

exercise_IntroToIsos :: Spec
exercise_IntroToIsos = do
  it "1. choose optics" $ do
    -- For each of the following tasks, choose whether it’s best suited
    -- to a Lens, Traversal, Prism, or Iso:
    --
    -- • Focus a Celsius temperature in Fahrenheit
    -- A: iso

    -- • Focus the last element of a list
    -- A: prism

    -- • View a JSON object as its corresponding Haskell Record
    -- A: prism if we want to handle errors, otherwise iso

    -- • Rotate the elements of a three-tuple one to the right
    -- A: iso

    -- • Focus on the ‘bits’ of an Int as Bools.
    -- A: iso

    -- • Focusing an IntSet from a Set Int
    -- A: I'm not sure what IntSet is, but I guess it should be 'iso'.
    True

  it "2. fill in the blank" $ do
    ("Beauty", "Age") ^. swapped `shouldBe` ("Age", "Beauty")
    50 ^. from (adding 10) `shouldBe` 40
    0 & multiplying 4 +~ 12 `shouldBe` 3.0
    0 & adding 10 . multiplying 2 .~ 24 `shouldBe` 2
    [1, 2, 3] & reversed %~ tail `shouldBe` [1, 2]
    view flipped (++) [1, 2] [3, 4] `shouldBe` [3, 4, 1, 2]
    [1, 2, 3] ^. reversed `shouldBe` [3, 2, 1]
    -- bonus
    [[1, 2, 3], [10, 20, 30]] & involuted transpose %~ tail
      `shouldBe` [[2, 3], [20, 30]]
    let switchCase c = if isUpper c then toLower c else toUpper c
    (32, "Hi") & _2 . involuted (map switchCase) .~ ("hELLO" :: String)
      `shouldBe` (32, "Hello")

  it "3. implement fahrenheit lens" $ do
    let c2F (c :: Double) = (c * (9 / 5)) + 32
    -- I literally just paraphrased c2F!
    let f2C (f :: Double) = review (multiplying (9 / 5) . adding 32) f
    let fahrenheit = iso c2F f2C
    let fahrenheit' = iso c2F f2C
    -- because of some haskell type checker limitations, i wasn't able to use
    -- the same fahrenheit twice
    0.0 ^. fahrenheit' `shouldBe` 32.0
    100.0 ^. from fahrenheit `shouldBe` 37.777777777777778

    -- alternatively, we can just combine other isos
    let fahrenheit2 = multiplying (9 / 5) . adding 32
    let fahrenheit2' = multiplying (9 / 5) . adding 32
    0.0 ^. fahrenheit2 `shouldBe` 32.0
    100.0 ^. from fahrenheit2' `shouldBe` 37.777777777777778

exercise_ProjectedIsos :: Spec
exercise_ProjectedIsos = do
  it "1. Fill in the blank" $ do
    ("Beauty", "Age") ^. mapping reversed . swapped
      `shouldBe` ("egA", "Beauty")

    [True, False, True] ^. mapping (involuted not)
      `shouldBe` [False, True, False]

    [True, False, True] & mapping (involuted not) %~ filter id
      `shouldBe` [False]

    -- a function is a covariant functor on its return type
    (show ^. mapping reversed) 1234
      `shouldBe` "4321"

  it "2. implement intNot with dimapping" $ do
    intNot 0 `shouldBe` 1
    intNot 1 `shouldBe` 0
    evaluate (intNot 2) `shouldThrow` anyException

    intNot' 0 `shouldBe` 1
