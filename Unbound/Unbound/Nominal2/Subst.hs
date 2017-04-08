{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , GADTs
           , ScopedTypeVariables
           , RankNTypes
  #-}

module Unbound.Nominal2.Subst where

import Generics.RepLib

import Unbound.Nominal2.Name
import Unbound.Nominal2.Alpha
import Unbound.Nominal2.Types
import Unbound.Nominal2.Fresh

data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b

class (Rep1 (SubstD b) a) => Subst b a where
  isvar :: a -> Maybe (SubstName a b)
  isvar _ = Nothing

  subst :: (Fresh m) => Name b -> b -> a -> m a
  subst n u x =
    case (isvar x :: Maybe (SubstName a b)) of
      Just (SubstName m) -> return $ if m == n then u else x
      Nothing -> substR1 rep1 n u x

data SubstD b a = SubstD {
  isvarD :: a -> Maybe (SubstName a b)
  , substD :: forall m. (Fresh m) => Name b -> b -> a -> m a
}

instance Subst b a => Sat (SubstD b a) where
  dict = SubstD isvar subst

-----------------------------------------
-- Generic Implementations
-----------------------------------------
substR1 :: (Fresh m) => R1 (SubstD b) a -> Name b -> b -> a -> m a
substR1 (Data1 _ cons) = \n u d ->
  case (findCon cons d) of
    Val c rec kids -> do
      kids' <- (mapM_l (\w -> substD w n u) rec kids)
      return $ to c kids'
substR1 _ = \_ _ d -> return d

instance Subst b Int
instance Subst b Bool
instance Subst b ()
instance Subst b Char
instance Subst b Integer
instance Subst b Float
instance Subst b Double

instance Subst b AnyName
instance Rep a => Subst b (R a)
instance Rep a => Subst b (Name a)

instance (Subst c a, Subst c b) => Subst c (a,b)
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d)
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e)
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f)
instance (Subst c a) => Subst c [a]
instance (Subst c a) => Subst c (Maybe a)
instance (Subst c a, Subst c b) => Subst c (Either a b)

------------------------------------------
-- Test code
------------------------------------------

instance Subst Expr Expr
