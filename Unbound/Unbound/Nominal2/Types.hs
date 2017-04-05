{-# LANGUAGE TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , EmptyDataDecls
  #-}

module Unbound.Nominal2.Types (
  Bind(..)
  , Rec(..)
  , Embed(..)
) where

import Generics.RepLib
import Unbound.Nominal2.Name

data Bind p t = Bind p t
  deriving (Show)

data Rec p = Rec p
  deriving (Show)

newtype Embed t = Embed t
  deriving (Show)

$(derive [''Bind, ''Embed, ''Rec])
