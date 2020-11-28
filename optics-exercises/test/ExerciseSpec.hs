{- HLINT ignore "Use camelCase" -}
{- HLINT ignore "Redundant $" -}
{- HLINT ignore "Redundant do" -}
module ExerciseSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Control.Lens hiding ((&))
import Control.Lens.Properties

import Data.Char (toUpper, toLower, isAlpha)
import qualified Data.Map as M
import qualified Data.Set as S
-- import qualified Data.Text as T
import Data.Monoid
import Data.Ord
import Data.Function hiding ((&))
import Control.Applicative
import Control.Monad.State

import Exercise

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
  it "2. change the type of the best and worst fields" $
    -- polymorphic lens laws do not type check, so I'll only test for
    -- the cases when a ~ b.
    isLens (preferenceLens @String @String)
    .&.
    isLens (preferenceLens @Int @Int)

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
    view (_2._1._2) ("Ginerva", (("Galileo", "Waldo"), "Malfoy")) `shouldBe`
    "Waldo"

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
    let goalA = Kingdom { _name = "Duloc: a perfect place" , _army = Army { _archers = 22 , _knights = 42 } , _gate = Gate { _open = False , _oilTemp = 10.0 } }
    let goalA' = duloc & name <>~ ": a perfect place"
                       & army.knights .~ 42
                       & gate.open %~ not
    goalA' `shouldBe` goalA

  it "1.2 reach goal B" $ do
    let goalB = Kingdom { _name = "Dulocinstein" , _army = Army { _archers = 17 , _knights = 26 } , _gate = Gate { _open = True , _oilTemp = 100.0}}
    let goalB' = duloc & name .~ "Dulocinstein"
                       & army.archers -~ 5
                       & army.knights *~ 2
                       & army.knights -~ 2
                       & gate.oilTemp ^~ 2
    goalB' `shouldBe` goalB

  it "1.3 reach goal C" $ do
    let goalC = ("Duloc: Home", Kingdom { _name = "Duloc: Home of the talking Donkeys" , _army = Army { _archers = 22 , _knights = 14 } , _gate = Gate { _open = True , _oilTemp = 5.0 } })
    let goalC' = duloc & name .~ "Duloc: Home"
                       & gate.oilTemp -~ 5
                       & name <<<>~ " of the talking Donkeys"
    goalC' `shouldBe` goalC

  it "2.1 fill in undefined" $ do
    let goal = (True, "opossums")
    let goal' = (False, "opossums") & _1 ||~ True
    goal' `shouldBe` goal

  it "2.2 fill in undefined" $ do
    let goal = ((False,"DUDLEY - THE WORST"),20.0)
    let goal' = ((True, "Dudley"), 55.0) & _1 . _2 <>~ " - the worst"
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
    beastSizes ^.. folded.folded `shouldBe` ["Sirens", "Kraken", "Ogopogo"]
    beastSizes ^.. folded.folded.folded `shouldBe` "SirensKrakenOgopogo"
    beastSizes ^.. folded._2 `shouldBe` beastSizes ^.. folded.folded
    toListOf (folded.folded) [[1,2,3],[4,5,6]] `shouldBe` [1,2,3,4,5,6]
    toListOf (folded.folded) (M.fromList [("Jack", "Captain"), ("Will", "First Mate")])
      `shouldBe` "CaptainFirst Mate"
    ("Hello", "It's me") ^.. both.folded `shouldBe` "HelloIt's me"
    ("Why", "So", "Serious?") ^.. each `shouldBe` ["Why", "So", "Serious?"]
    let quotes = [("Why", "So", "Serious?"), ("This", "is", "SPARTA")]
    quotes ^.. each.each.each `shouldBe` "WhySoSerious?ThisisSPARTA"

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
    [1, 2, 3] ^.. folded `shouldBe` [1,2,3]
    [1, 2, 3] ^.. id `shouldBe` [[1,2,3]]
    ("Light", "Dark") ^.. _1 `shouldBe` ["Light"]
    [("Light", "Dark"), ("Happy", "Sad")] ^.. folded.both
      `shouldBe` ["Light", "Dark", "Happy", "Sad"]
    [("Light", "Dark"), ("Happy", "Sad")] ^.. folded._1
      `shouldBe` ["Light", "Happy"]
    [("Light", "Dark"), ("Happy", "Sad")] ^.. folded._2.folded
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
      `shouldBe` [[1,2], [4,5]]
    ["bob", "otto", "hannah"] ^.. folded . to reverse
      `shouldBe` ["bob", "otto", "hannah"]
    ("abc", "def") ^.. folding (\(a, b) -> [a, b]). to reverse . folded
      `shouldBe` "cbafed"

  it "2. fill in the blanks" $ do
    [1..5] ^.. folded . to (*100)
      `shouldBe` [100,200,300,400,500]

    (1, 2) ^.. both
      `shouldBe` [1, 2]

    [(1, "one"), (2, "two")] ^.. folded._2
      `shouldBe` ["one", "two"]

    (Just 1, Just 2, Just 3) ^.. each.folded
      `shouldBe` [1, 2, 3]

    [Left 1, Right 2, Left 3] ^.. folded.folded
      `shouldBe` [2]

    [([1, 2], [3, 4]), ([5, 6], [7, 8])] ^.. folded.both.folded
      `shouldBe` [1, 2, 3, 4, 5, 6, 7, 8]

    [1, 2, 3, 4] ^.. folding (\[a,b,c,d] -> [(a,b), (c,d)]) .
                     folding (\(a,b) -> [Left a, Right b])
      `shouldBe` [Left 1, Right 2, Left 3, Right 4]

    [(1, (2, 3)), (4, (5, 6))] ^.. folded.folding (\(a,(b,c)) -> [a,b,c])
      `shouldBe` [1, 2, 3, 4, 5, 6]

    [(Just 1, Left "one"), (Nothing, Right 2)] ^.. folded .
                                                   folding (\(a,b) -> [a^..folded, b^..folded]) .
                                                   folded
      `shouldBe` [1, 2]

    [(1, "one"), (2, "two")] ^.. folded . folding (\(a,b) -> [Left a, Right b])
      `shouldBe` [Left 1, Right "one", Left 2, Right "two"]
    S.fromList ["apricots", "apples"] ^.. folded . folding reverse
      `shouldBe` "selppastocirpa"

  it "3. (bonus) Devise a fold which returns the expected results." $ do
    [(12, 45, 66), (91, 123, 87)] ^.. folded._2.folding (reverse.show)
      `shouldBe` "54321"

    [(1,"a"),(2,"b"),(3,"c"),(4,"d")] ^..
      folded.folding (\(a,b) -> if even a then Just b else Nothing)
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
    let output3 = Just (3,"Be")
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
    foldOf (reversed.folded) input2
      `shouldBe` output2

    let input3 = [(12, 45, 66), (91, 123, 87)]
    let output3 = "54321"
    foldOf (folded._2.to show.reversed) input3
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
      `shouldBe` ["My","Hakuna","No"]


    ["My Precious", "Hakuna Matata", "No problemo"] ^.. taking 1 (folded . worded)
      `shouldBe` ["My"]

    ["My Precious", "Hakuna Matata", "No problemo"] ^.. folded . taking 1 worded . folded
      `shouldBe` "MyHakunaNo"

    ["My Precious", "Hakuna Matata", "No problemo"] ^.. folded . takingWhile isAlpha folded
      `shouldBe` "MyHakunaNo"

    sumOf (taking 2 each) (10, 50, 100)
      `shouldBe` 60

    ("stressed", "guns", "evil") ^.. backwards each
      `shouldBe` ["evil","guns","stressed"]

    ("stressed", "guns", "evil") ^.. backwards each . to reverse
      `shouldBe` ["live","snug","desserts"]

    "blink182 k9 blazeit420" ^.. worded . droppingWhile isAlpha folded
      `shouldBe` "1829420"

  describe "2. solve the problems" $ do
    let sample = [-10, -5, 4, 3, 8, 6, -2, 3, -5, -7] :: [Int]

    it "find # of days it took to thaw" $ do
      lengthOf (takingWhile (<0) folded) sample `shouldBe` 2

    it "warmest temperature in first 4 days" $ do
      maximumOf (taking 4 each) sample `shouldBe` Just 4

    it "the temperature after the warmest day in the 4 days" $ do
      let maxTemp = 4
      sample ^? dropping 1 (droppingWhile (/= maxTemp) each) `shouldBe` Just 3

    it "how many freezing days at the end" $ do
      lengthOf (takingWhile (<0) (reversed.each)) sample `shouldBe` 2

    it "list the days from first thaw to next freeze" $ do
      sample ^.. takingWhile (>= 0) (droppingWhile (<0) each)
        `shouldBe` [4,3,8,6]

    it "bonus: list the days from first thaw to last freeze" $ do
      sample ^.. backwards (droppingWhile (<0) $ backwards $ droppingWhile (<0) each)
        `shouldBe` [4,3,8,6,-2,3]

      let trimmingWhile p = backwards.droppingWhile p.backwards.droppingWhile p
      sample ^.. trimmingWhile (<0) each
        `shouldBe` [4,3,8,6,-2,3]


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
    let card = deck ^? folded
                     . filteredBy (moves . to length . filtered (>1))
                     . cardName
    card `shouldBe` Just "Kapichu"

  it "find any Hot cards with a move with more than 30 power" $ do
    let card = deck ^? folded
                     . filteredBy (aura . only Hot)
                     . filteredBy (moves . folded . movePower . filtered (>30))
                     . cardName
    card `shouldBe` Just "Spicyeon"

  it "list all names of holographic cards with a Wet aura" $ do
    let cards = deck ^.. folded
                       . filteredBy (aura . only Wet)
                       . filteredBy (holo . only True)
                       . cardName
    cards `shouldBe` ["Garydose"]

  it "find sum of all attack power belonging to non-leafy cards" $ do
    let power = flip sumOf deck $ folded
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
      (("Jurassic", "Park") & both . traversed .~ 'x') `shouldBe`
        ("xxxxxxxx", "xxxx")
    it "3" $ do
      (("Malcolm", ["Kaylee", "Inara", "Jayne"]) & beside id traversed %~ take 3)
        `shouldBe` ("Mal", ["Kay", "Ina", "Jay"])
    it "4" $ do
      (("Malcolm", ["Kaylee", "Inara", "Jayne"]) & _2 . element 1 .~ "River")
        `shouldBe` ("Malcolm", ["Kaylee", "River", "Jayne"])
    it "5" $ do
      let result = ["Die Another Day", "Live and Let Die", "You Only Live Twice"]
            & traversed . elementOf worded 1 . traversed .~ 'x'
      result `shouldBe` [ "Die xxxxxxx Day"
                        , "Live xxx Let Die"
                        , "You xxxx Live Twice"
                        ]
    it "6" $ do
      let result = ((1, 2), (3, 4)) & beside both both +~ 1
      result `shouldBe` ((2, 3), (4, 5))

    it "7" $ do
      let result = (1, (2, [3, 4])) & beside id (beside id each) +~ 1
      result `shouldBe` (2, (3, [4, 5]))

    it "8" $ do
      let result = ((True, "Strawberries"), (False, "Blueberries"), (True, "Blackberries"))
            & each . filtered fst . _2 . taking 5 traversed %~ toUpper
      result `shouldBe`
        ((True, "STRAWberries"), (False, "Blueberries"), (True, "BLACKberries"))

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
      result `shouldBe` ZipList [[1,3], [2,4]]
    it "4" $ do
      let result = sequenceAOf (traversed . _2) [('a', ZipList [1,2]), ('b', ZipList [3,4])]
      result `shouldBe` ZipList [[('a',1),('b',3)],[('a',2),('b',4)]]
    it "5" $ do
      let input = ([1, 1, 1], (1, 1))
      let traversal = beside each both
      let result = traverseOf traversal (\n -> modify (+n) >> get) input
      runState result 0 `shouldBe` (([1,2,3],(4,5)), 5)

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
          where validate age | age <= 0   = Left "Age must be greater than 0"
                             | age >= 150 = Left "Age must be less than 150"
                             | otherwise  = Right age
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
  let transactions = [Deposit 10, Withdrawal  20, Deposit 30]
  it "1. rewrite amount transaction" $ do
    let transactions' = transactions & traversed . amountT %~ (+1)
    transactions' `shouldBe` [Deposit 11, Withdrawal 21, Deposit 31]

  it "2. rewrite both" $ do
    ((1, 2) & bothT %~ (* 5)) `shouldBe` (5, 10)

  it "3. rewrite transaction delta" $ do
    (Deposit 10 ^? transactionDelta) `shouldBe` Just 10
    (Withdrawal 10 ^? transactionDelta) `shouldBe` Just (-10)
    (Deposit 10 & transactionDelta .~ 15) `shouldBe` Deposit 15
    (Withdrawal 10 & transactionDelta .~ (-15)) `shouldBe ` Withdrawal 15
    (Deposit 10 & transactionDelta +~ 5) `shouldBe` Deposit 15
    (Withdrawal 10 & transactionDelta +~ 5) `shouldBe ` Withdrawal 5

  it "4. implement left" $ do
    (Left 5 & leftT +~ 5) `shouldBe` (Left 10 :: Either Int Int)
    (Right 5 & leftT +~ 5) `shouldBe` (Right 5 :: Either Int Int)
    (Left 5 & leftT .~ 10) `shouldBe` (Left 10 :: Either Int Int)
    (Right 5 & leftT +~ 10) `shouldBe` (Right 5 :: Either Int Int)

  it "5. Bonus: Reimplement beside" $
    (((1, 2), 3) & besideT both id +~ 3) `shouldBe` ((4, 5), 6)

exercise_TraversalLaws :: Spec
exercise_TraversalLaws = do
  it "1. which law does worded break?" $ do
    -- it breaks the "coherent focus" law.
    ("foo bar" & worded <>~ " baz" & worded <>~ "a") `shouldBe` "fooa baza bara baza"
    ("foo bar" & worded <>~ "a baz") `shouldBe` "fooa baz bara baz"

  it "2. break the first law!" $ do
    (5 & law1BreakingT %%~ pure) `shouldNotBe` (pure 5 :: [Int])

  it "3. break the second law!" $ do
    (2 & law2BreakingT %~ (`div` 2) & law2BreakingT %~ (+1))
      `shouldNotBe`
      (2 & law2BreakingT %~ ((+1) . (`div` 2)))
    (2 & filtered even %~ (`div` 2) & filtered even %~ (+1))
      `shouldNotBe`
      (2 & filtered even %~ ((+1) . (`div` 2)))

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

    it "lined" $ do
      -- not lawful. same reason as worded
      ("foo\nbar" & lined <>~ "\nbaz" & lined <>~ "X")
      `shouldNotBe`
        ("foo\nbar" & lined <>~ "X\nbaz")

    it "traversed" $ do
      -- lawful
      True

exercise_PartsOf :: Spec
exercise_PartsOf = do
  it "fill in the blanks" $ do
    [1,2,3,4] ^. partsOf (traversed . filtered even)
      `shouldBe` [2,4]

    ["Aardvark", "Bandicoot", "Capybara"]
      -- the original book uses "^." which doesn't type check
      ^.. traversed . partsOf (taking 3 traversed)
      `shouldBe` ["Aar", "Ban", "Cap"]

    ([1, 2], M.fromList [('a', 3), ('b', 4)])
      ^. partsOf (beside each each)
      `shouldBe` [1,2,3,4]

    [1, 2, 3, 4] & partsOf (traversed . filtered even) .~ [20, 40]
      `shouldBe` [1,20,3,40]
