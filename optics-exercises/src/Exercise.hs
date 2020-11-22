{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

module Exercise where

import Control.Lens
import Control.Applicative
import Data.Char
import Data.Data.Lens
import Data.Maybe
import Text.Read
import Numeric.Lens
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T


------- Exercises: Laws -------------

-- Lens laws:
-- 1. view $ set a = a   (set-get)
-- 2. set $ view s = s   (get-set)
-- 3. set x $ set x = set x (set-set)

-- Implement a lens which breaks the second and/or third law. That’s
-- get-set and set-set respectively.
unlawful2 :: Lens' String Int
unlawful2 = lens getter setter
  where getter str = fromMaybe 0 (readMaybe str)
        setter _str int = show int

unlawful3 :: Lens' Int Int
unlawful3 = lens undefined setter
  where setter s _ = succ s


data Err = ReallyBadError { _msg :: String }
         | ExitCode { _code :: Int }
         deriving (Eq, Show)

msg :: Lens' Err String
msg = lens getMsg setMsg
  where
    getMsg (ReallyBadError message) = message
    getMsg (ExitCode _) = ""
    setMsg (ReallyBadError _) newMessage = ReallyBadError newMessage
    setMsg (ExitCode n) newMessage = ExitCode n

-- an alternative implementation that passes set-get and set-set but
-- fails get-set.
msg' :: Lens' Err String
msg' = lens getMsg setMsg
  where
    getMsg (ReallyBadError message) = message
    getMsg (ExitCode n) = show n
    setMsg (ReallyBadError _) newMessage = ReallyBadError newMessage
    setMsg (ExitCode n) newMessage = ReallyBadError newMessage

data Prenu = Prenu { _cmene :: String, _nilciho :: Int }
  deriving (Show, Eq)

prenuNilciho :: Lens' Prenu Int
prenuNilciho = lens getter setter
  where getter = _nilciho
        setter prenu i = prenu { _nilciho = clamp 0 100 i }
        clamp minVal maxVal = min maxVal . max minVal

breakAllLaws :: Lens' Int Int
breakAllLaws = lens (+1) (+)

data Builder = Builder
               { _context :: [String]
               , _build   :: [String] -> String
               }

builderLens :: Lens' Builder String
builderLens = lens getter setter
  where getter bld = _build bld $ _context bld
        setter (Builder ctx bld) val =
          let bld' = \ctx' -> if ctx == ctx'
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
    where bldEq c1 b1 b2 =
            b1 [] == b2 []
            && b1 c1 == b2 c1
            && b1 (c1 <> c1) == b2 (c1 <> c1)
            && b1 (c1 <> ["A", "B"]) == b2 (c1 <> ["A", "B"])


------- Exercises: Virtual Fields -------------
data User = User
            { _firstName :: String
            , _lastName :: String
         -- , _username :: String
            , _email :: String
            }
            deriving (Show, Eq)
makeLenses ''User

username' :: Lens' User String
username' = email

fullName :: Lens' User String
fullName = lens getter setter
  where
    getter u = unwords [view firstName u, view lastName u]
    setter u s = let first = words s ^. to head
                     last = words s ^. to (unwords . tail)
                 in u { _firstName = first, _lastName = last }

------- Exercises: Self-Correcting Lens -------

data ProducePrices =
  ProducePrices { _limePrice :: Float
                , _lemonPrice :: Float
                }
  deriving (Show, Eq)

makeLenses ''ProducePrices

priceLens :: Lens' ProducePrices Float ->
             Lens' ProducePrices Float ->
             Lens' ProducePrices Float
priceLens selfLens otherLens = lens getter setter
  where getter u = u ^. selfLens
        setter u v = let price' = selfPriceNormalized v
                         otherPrice = u ^. otherLens
                         otherPrice' = otherPriceNormalized price' otherPrice
                     in u & selfLens  .~ price'
                          & otherLens .~ otherPrice'
        selfPriceNormalized p = if p < 0 then 0.0 else p
        otherPriceNormalized p p' = if abs (p - p') <= 0.5
                                    then p'
                                    else p - 0.5 * signum (p - p')

limePrice' :: Lens' ProducePrices Float
limePrice' = priceLens limePrice lemonPrice

lemonPrice' :: Lens' ProducePrices Float
lemonPrice' = priceLens lemonPrice limePrice

----- Exercises: Polymorhic Lenses
data Preferences a = Preferences { _best :: a , _worst :: a }
  deriving Show
makeLenses ''Preferences

preferenceLens :: Lens (Preferences a) (Preferences b) (a, a) (b, b)
preferenceLens = lens getter setter
  where getter p = (p ^. best, p ^. worst)
        setter p (a1, a2) = p { _best = a1, _worst = a2 }

data Predicate a = Predicate (a -> Bool)

predLens :: Lens (Predicate a) (Predicate b) (a -> Bool) (b -> Bool)
predLens = lens getter setter
  where getter (Predicate f) = f
        setter (Predicate _) g = Predicate g

------- Exercises - Operators
data Gate = Gate { _open :: Bool
                 , _oilTemp :: Float }
          deriving (Eq, Show)
makeLenses ''Gate

data Army = Army { _archers :: Int
                 , _knights :: Int }
          deriving (Eq, Show)
makeLenses ''Army

data Kingdom = Kingdom { _name :: String
                       , _army :: Army
                       , _gate :: Gate }
             deriving (Eq, Show)
makeLenses ''Kingdom


duloc :: Kingdom
duloc = Kingdom { _name = "Duloc"
                , _army = Army { _archers = 22 , _knights = 14 }
                , _gate = Gate { _open = True , _oilTemp = 10.0 }
                }

--- Exercises: Filtering
-- A data structure to represent a single card
data Card = Card { _cardName :: String , _aura :: Aura , _holo :: Bool , _moves :: [Move] } deriving (Show, Eq)
-- Each card has an aura-type
data Aura = Wet | Hot | Spark | Leafy deriving (Show, Eq)
-- Cards have attack moves
data Move = Move { _moveName :: String , _movePower :: Int } deriving (Show, Eq)

makeLenses ''Card
makeLenses ''Move

deck :: [Card]
deck =  [ Card "Skwortul"    Wet   False [Move "Squirt" 20]
        , Card "Scorchander" Hot   False [Move "Scorch" 20]
        , Card "Seedasaur"   Leafy False [Move "Allergize" 20]
        , Card "Kapichu"     Spark False [Move "Poke" 10, Move "Zap" 30]
        , Card "Elecdude"    Spark False [Move "Asplode" 50]
        , Card "Garydose"    Wet   True  [Move "Gary's move" 40]
        , Card "Moisteon"    Wet   False [Move "Soggy" 3]
        , Card "Grasseon"    Leafy False [Move "Leaf Cut" 30]
        , Card "Spicyeon"    Hot   False [Move "Capsaicisize" 40]
        , Card "Sparkeon"    Spark True  [Move "Shock" 40, Move "Battery" 50]
        ]

---- Exercises: Traversal Actions
data UserT = UserT {_userName :: String, _age :: Int} deriving (Show, Eq)

makeLenses ''UserT

data Account = Account {_accountId :: String, _user :: UserT} deriving (Show, Eq)

makeLenses ''Account
