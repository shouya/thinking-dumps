{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

module Lib
  ( module Control.Lens
  , module Control.Applicative
  , module Numeric.Lens
  , module Data.Char
  , module Data.Data.Lens
  , someFunc
  )
where

import Control.Lens
import Control.Applicative
import Data.Char
import Data.Data.Lens
import Numeric.Lens
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T

someFunc :: IO ()
someFunc = putStrLn "someFunc"
