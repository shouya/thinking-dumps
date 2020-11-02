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
