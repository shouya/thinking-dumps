{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Exercise where

import Control.Lens
import Control.Monad.State.Lazy
import Data.Char
import Data.List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Lens
import Text.Read hiding (get)

------- Exercises: Laws -------------

-- Lens laws:
-- 1. view $ set a = a   (set-get)
-- 2. set $ view s = s   (get-set)
-- 3. set x $ set x = set x (set-set)

-- Implement a lens which breaks the second and/or third law. That’s
-- get-set and set-set respectively.
unlawful2 :: Lens' String Int
unlawful2 = lens getter setter
  where
    getter str = fromMaybe 0 (readMaybe str)
    setter _str int = show int

unlawful3 :: Lens' Int Int
unlawful3 = lens undefined setter
  where
    setter s _ = succ s

data Err
  = ReallyBadError {_msg :: String}
  | ExitCode {_code :: Int}
  deriving (Eq, Show)

msg :: Lens' Err String
msg = lens getMsg setMsg
  where
    getMsg (ReallyBadError message) = message
    getMsg (ExitCode _) = ""
    setMsg (ReallyBadError _) newMessage = ReallyBadError newMessage
    setMsg (ExitCode n) _newMessage = ExitCode n

-- an alternative implementation that passes set-get and set-set but
-- fails get-set.
msg' :: Lens' Err String
msg' = lens getMsg setMsg
  where
    getMsg (ReallyBadError message) = message
    getMsg (ExitCode n) = show n
    setMsg (ReallyBadError _) newMessage = ReallyBadError newMessage
    setMsg (ExitCode _n) newMessage = ReallyBadError newMessage

data Prenu = Prenu {_cmene :: String, _nilciho :: Int}
  deriving (Show, Eq)

prenuNilciho :: Lens' Prenu Int
prenuNilciho = lens getter setter
  where
    getter = _nilciho
    setter prenu i = prenu {_nilciho = clamp 0 100 i}
    clamp minVal maxVal = min maxVal . max minVal

breakAllLaws :: Lens' Int Int
breakAllLaws = lens (+ 1) (+)

data Builder = Builder
  { _context :: [String],
    _build :: [String] -> String
  }

builderLens :: Lens' Builder String
builderLens = lens getter setter
  where
    getter bld = _build bld $ _context bld
    setter (Builder ctx bld) val =
      let bld' = \ctx' ->
            if ctx == ctx'
              then val
              else bld ctx'
       in Builder ctx bld'

instance Show Builder where
  show b = concat ["Builder { _context = ", show $ _context b, "}"]

-- the implementation is not complete, I only checked some
-- characteristic values for the _build function.
instance Eq Builder where
  (Builder c1 b1) == (Builder c2 b2) =
    c1 == c2 && bldEq c1 b1 b2
    where
      bldEq c1 b1 b2 =
        b1 [] == b2 []
          && b1 c1 == b2 c1
          && b1 (c1 <> c1) == b2 (c1 <> c1)
          && b1 (c1 <> ["A", "B"]) == b2 (c1 <> ["A", "B"])

------- Exercises: Virtual Fields -------------
data User = User
  { _firstName :: String,
    _lastName :: String,
    -- , _username :: String
    _email :: String
  }
  deriving (Show, Eq)

makeLenses ''User

username' :: Lens' User String
username' = email

fullName :: Lens' User String
fullName = lens getter setter
  where
    getter u = unwords [view firstName u, view lastName u]
    setter u s =
      let first = words s ^. to head
          last = words s ^. to (unwords . tail)
       in u {_firstName = first, _lastName = last}

------- Exercises: Self-Correcting Lens -------

data ProducePrices = ProducePrices
  { _limePrice :: Float,
    _lemonPrice :: Float
  }
  deriving (Show, Eq)

makeLenses ''ProducePrices

priceLens ::
  Lens' ProducePrices Float ->
  Lens' ProducePrices Float ->
  Lens' ProducePrices Float
priceLens selfLens otherLens = lens getter setter
  where
    getter u = u ^. selfLens
    setter u v =
      let price' = selfPriceNormalized v
          otherPrice = u ^. otherLens
          otherPrice' = otherPriceNormalized price' otherPrice
       in u & selfLens .~ price'
            & otherLens .~ otherPrice'
    selfPriceNormalized p = if p < 0 then 0.0 else p
    otherPriceNormalized p p' =
      if abs (p - p') <= 0.5
        then p'
        else p - 0.5 * signum (p - p')

limePrice' :: Lens' ProducePrices Float
limePrice' = priceLens limePrice lemonPrice

lemonPrice' :: Lens' ProducePrices Float
lemonPrice' = priceLens lemonPrice limePrice

----- Exercises: Polymorhic Lenses
data Preferences a = Preferences {_best :: a, _worst :: a}
  deriving (Show)

makeLenses ''Preferences

preferenceLens :: Lens (Preferences a) (Preferences b) (a, a) (b, b)
preferenceLens = lens getter setter
  where
    getter p = (p ^. best, p ^. worst)
    setter p (a1, a2) = p {_best = a1, _worst = a2}

newtype Predicate a = Predicate (a -> Bool)

predLens :: Lens (Predicate a) (Predicate b) (a -> Bool) (b -> Bool)
predLens = lens getter setter
  where
    getter (Predicate f) = f
    setter (Predicate _) g = Predicate g

------- Exercises - Operators
data Gate = Gate
  { _open :: Bool,
    _oilTemp :: Float
  }
  deriving (Eq, Show)

makeLenses ''Gate

data Army = Army
  { _archers :: Int,
    _knights :: Int
  }
  deriving (Eq, Show)

makeLenses ''Army

data Kingdom = Kingdom
  { _name :: String,
    _army :: Army,
    _gate :: Gate
  }
  deriving (Eq, Show)

makeLenses ''Kingdom

duloc :: Kingdom
duloc =
  Kingdom
    { _name = "Duloc",
      _army = Army {_archers = 22, _knights = 14},
      _gate = Gate {_open = True, _oilTemp = 10.0}
    }

--- Exercises: Filtering
-- A data structure to represent a single card
data Card = Card
  { _cardName :: String,
    _aura :: Aura,
    _holo :: Bool,
    _moves :: [Move]
  }
  deriving (Show, Eq)

-- Each card has an aura-type
data Aura = Wet | Hot | Spark | Leafy deriving (Show, Eq)

-- Cards have attack moves
data Move = Move {_moveName :: String, _movePower :: Int} deriving (Show, Eq)

makeLenses ''Card
makeLenses ''Move

deck :: [Card]
deck =
  [ Card "Skwortul" Wet False [Move "Squirt" 20],
    Card "Scorchander" Hot False [Move "Scorch" 20],
    Card "Seedasaur" Leafy False [Move "Allergize" 20],
    Card "Kapichu" Spark False [Move "Poke" 10, Move "Zap" 30],
    Card "Elecdude" Spark False [Move "Asplode" 50],
    Card "Garydose" Wet True [Move "Gary's move" 40],
    Card "Moisteon" Wet False [Move "Soggy" 3],
    Card "Grasseon" Leafy False [Move "Leaf Cut" 30],
    Card "Spicyeon" Hot False [Move "Capsaicisize" 40],
    Card "Sparkeon" Spark True [Move "Shock" 40, Move "Battery" 50]
  ]

---- Exercises: Traversal Actions
data UserT = UserT {_userName :: String, _age :: Int} deriving (Show, Eq)

makeLenses ''UserT

data Account = Account {_accountId :: String, _user :: UserT} deriving (Show, Eq)

makeLenses ''Account

---- Exercises: Custom traversals
data Transaction
  = Withdrawal {_amount :: Int}
  | Deposit {_amount :: Int}
  deriving (Show, Eq)

makeLenses ''Transaction

newtype BankAccount = BankAccount {_transactions :: [Transaction]}
  deriving (Show, Eq)

makeLenses ''BankAccount

amountT :: Traversal' Transaction Int
amountT handler (Withdrawal amt) = Withdrawal <$> handler amt
amountT handler (Deposit amt) = Deposit <$> handler amt

bothT :: Traversal (a, a) (b, b) a b
-- bothT :: (a -> s b) -> (a, a) -> s (b, b)
bothT f (x, y) = (,) <$> f x <*> f y

transactionDelta :: Traversal' Transaction Int
transactionDelta handler (Withdrawal amt) = Withdrawal . negate <$> handler (- amt)
transactionDelta handler (Deposit amt) = Deposit <$> handler amt

leftT :: Traversal (Either a b) (Either a' b) a a'
-- leftT :: (a -> s a') -> Either a b -> s (Either a b')
leftT f (Left v) = Left <$> f v
leftT _f (Right v) = pure $ Right v

besideT ::
  Traversal s t a b ->
  Traversal s' t' a b ->
  Traversal (s, s') (t, t') a b
besideT l r f (x, y) = (,) <$> l f x <*> r f y

------ Exercises: Traversal laws

law1BreakingT :: Traversal' Int Int
law1BreakingT f n = negate <$> f n

--- aka (filtered even)
law2BreakingT :: Traversal' Int Int
law2BreakingT f n
  | even n = f n
  | otherwise = pure n

----- Exercises: partsOf
--- I want to implement parts of on my own

-- (a -> f a) -> s -> f s
myPartsOf :: Traversal' s a -> Lens' s [a]
myPartsOf t = lens getter setter
  where
    getter s = s ^.. t
    -- setter :: s -> [a] -> s
    setter s xs = evalState (s & t %%~ assignElem) xs
    assignElem a = state $ \case
      [] -> (a, [])
      (x : xs) -> (x, xs)

-- thanks to: https://stackoverflow.com/a/65064222/1232832
myUnsafePartsOf :: Traversal s t a b -> Lens s t [a] [b]
myUnsafePartsOf traverse = lens getter setter
  where
    -- getter :: s -> [a]
    getter s = s ^.. (\f -> Const . getConst . traverse (Const . getConst . f))
    -- setter :: s -> [b] -> t
    setter s xs = evalState (s & traverse %%~ assignElem) xs
    assignElem _a = state $ \case
      [] -> error "list not long enough"
      (b : bs) -> (b, bs)

----- Exercises Custom Indexed Structures

--- task: implement a case-insensitive ix for map
newtype CIMap a = CIMap (Map String a)
  deriving (Eq, Show)

type instance Index (CIMap _) = String

type instance IxValue (CIMap a) = a

instance Ixed (CIMap a) where
  ix :: String -> Traversal' (CIMap a) a
  -- ix :: String -> forall f. (a -> f a) -> CIMap a -> f (CIMap a)
  ix key f (CIMap m) =
    case M.lookup lowerKey m of
      Just v -> (\v' -> CIMap (M.insert lowerKey v' m)) <$> f v
      Nothing -> pure (CIMap m)
    where
      lowerKey = map toLower key

--- For Exercises: Prisms
data ContactInfo = Email String | Telephone Int | Address String String String

makePrisms ''ContactInfo

--- For Exercises: Custom prisms
_Factor :: Int -> Prism' Int Int
_Factor n = prism' embed match
  where
    embed :: Int -> Int
    embed i = i * n
    match :: Int -> Maybe Int
    match i = if i `mod` n == 0 then Just (i `div` n) else Nothing

_Tail :: Prism' [a] [a]
_Tail = prism' embed match
  where
    embed :: [a] -> [a]
    embed xs = xs
    match :: [a] -> Maybe [a]
    match [] = Nothing
    match (_x : xs) = Just xs

_ListCons :: Prism [a] [b] (a, [a]) (b, [b])
_ListCons = prism embed match
  where
    embed (x, xs) = x : xs
    match [] = Left []
    match (x : xs) = Right (x, xs)

_Cycles :: Int -> Prism' String String
_Cycles n = prism' embed match
  where
    embed s = concat $ replicate n s
    match xs = extractCycle n xs
    extractCycle 0 [] = Just ""
    extractCycle 0 _xs = Nothing
    extractCycle 1 xs = Just xs
    extractCycle n xs
      | (length xs `mod` n) /= 0 = Nothing
      | otherwise =
        let len = length xs `div` n
            first = take len xs
         in case extractCycle (n - 1) (drop len xs) of
              Nothing -> Nothing
              Just first' | first == first' -> Just first
              _ -> Nothing

--- For exercises: Prism laws
_Contains :: Ord a => a -> Prism' (Set a) (Set a)
_Contains a = prism' embed match
  where
    embed s = S.insert a s
    match s =
      if S.member a s
        then Just (S.delete a s)
        else Nothing

_Singleton :: Prism' [a] a
_Singleton = prism' embed match
  where
    embed a = [a]
    match [a] = Just a
    match _ = Nothing

_PlusOne :: Prism' Int Int
_PlusOne = prism' embed match
  where
    embed n = n + 1
    match 0 = Nothing
    match n = Just $ n - 1

-- For exercise: Projected isos
-- instance Enum Bool
intNot :: Int -> Int
intNot = not ^. dimapping enum (from enum)

-- simplified
intNot' = fromEnum . not . toEnum

-- For exercise: Iso laws
mapList :: Ord k => Iso' (M.Map k v) [(k, v)]
mapList = iso M.toList M.fromList

nonEmptyList :: Iso' [a] (Maybe (NonEmpty a))
nonEmptyList = iso to from
  where
    to [] = Nothing
    to (x : xs) = Just (x :| xs)
    from Nothing = []
    from (Just (x :| xs)) = x : xs

sorted :: (Ord a) => Iso' [a] [(Int, a)]
sorted = iso to from
  where
    to xs = sortOn snd $ zip [0 ..] xs
    from xs = snd <$> sortOn fst xs

-- For exercise: Custom indexed optics
ipair :: IndexedFold Bool (a, a) a
ipair = ifolding (\(x, y) -> [(False, x), (True, y)])

ipair' :: IndexedTraversal Bool (a, a) (b, b) a b
ipair' p (x, y) = (,) <$> indexed p False x <*> indexed p True y

oneIndexed :: IndexedTraversal Int [a] [b] a b
oneIndexed = reindexed (+ 1) itraversed

oneIndexed' :: IndexedTraversal Int [a] [b] a b
oneIndexed' f xs = helper (1 :: Int) f xs
  where
    helper _ _ [] = pure []
    helper n f (x : xs) = (:) <$> indexed f n x <*> helper (n + 1) f xs

invertedIndex :: IndexedTraversal Int [a] [b] a b
invertedIndex =
  reindexed
    (\(xs, i) -> length xs - i - 1)
    (selfIndex <.> itraversed)

ichars :: IndexedTraversal Int Text Text Char Char
ichars = unpacked . itraversed

icharCoords :: IndexedTraversal (Int, Int) Text Text Char Char
icharCoords = unpacked . (lined <.> traversed)
