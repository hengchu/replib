{-# LANGUAGE RankNTypes
           , TemplateHaskell
           , GADTs
           , UndecidableInstances
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , ScopedTypeVariables
  #-}

module Unbound.Nominal2.Name (
  -- * Name types
  Name(..)
  , AnyName(..)

  -- * Constructing names
  , string2Name
  , s2n

  -- * Sorts
  , toSortedName
  , getR

  -- * Representations
  -- | Automatically generated by RepLib.
  , rR
  , rR1
  , rName
  , rName1
  , rAnyName
  , rAnyName1
) where

import Generics.RepLib

$(derive_abstract [''R])

-- |A name to be bound.
data Name a =
  Name (R a) (String, Maybe Integer)
  deriving (Eq, Ord)

$(derive [''Name])

-- |A name that hides the sort.
data AnyName = forall a. Rep a => AnyName (Name a)

$(derive_abstract [''AnyName])

instance Show AnyName where
  show (AnyName n) = show n

instance Eq AnyName where
  (AnyName n1) == (AnyName n2) =
    case gcastR (getR n1) (getR n2) n1 of
      Just n1' -> n1' == n2
      Nothing  -> False

instance Ord AnyName where
  compare (AnyName n1) (AnyName n2) =
    case compareR (getR n1) (getR n2) of
      EQ -> case gcastR (getR n1) (getR n2) n1 of
        Just n1' -> compare n1' n2
        Nothing -> error "Panic: equal types are not equal in Ord AnyName instance!"
      ord -> ord

------------------------------------------------------
-- Utilities
------------------------------------------------------

instance Show (Name a) where
  show (Name _ (x, Just idx)) = x ++ show idx
  show (Name _ (x, Nothing))  = x

-- |Get the sort representation of a name.
getR :: Name a -> R a
getR (Name r _) = r

-- |Cast a name with a hidden sort to an explicitly sorted name.
toSortedName :: Rep a => AnyName -> Maybe (Name a)
toSortedName (AnyName n) = gcastR (getR n) rep n

-- |Create a name with the given 'String' as the name.
string2Name :: Rep a => String -> Name a
string2Name s = Name rep (s, Nothing)

-- |Alias for 'string2Name'.
s2n :: Rep a => String -> Name a
s2n = string2Name
