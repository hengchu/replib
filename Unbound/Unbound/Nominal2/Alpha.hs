{-# LANGUAGE RankNTypes
           , FlexibleContexts
           , GADTs
           , TypeFamilies
           , TemplateHaskell
           , FlexibleInstances
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}

module Unbound.Nominal2.Alpha where

import Generics.RepLib hiding (GT)
import Unbound.PermM
import Unbound.Nominal2.Name
import Unbound.Nominal2.Types
import Unbound.Nominal2.Fresh
import Unbound.Util

import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isJust)
import qualified Data.List as L
import Data.Monoid

------------------------------------
-- Public API
------------------------------------

-- |Smart constructor for binder.
bind :: (Alpha p, Alpha t) => p -> t -> Bind p t
bind = Bind

-- |List the binding variables in a pattern.
binders :: (Rep a, Alpha a) => a -> [AnyName]
binders = binders' initial

fv :: (Alpha a) => a -> Set AnyName
fv = fv' initial

aeq :: (Alpha a) => a -> a -> Bool
aeq = aeq' initial

data AlphaD a = AlphaD {
  swapsD :: AlphaCtx -> Perm AnyName -> a -> a
  , swapallD :: AlphaCtx -> Perm AnyName -> a -> a
  , fvD :: AlphaCtx -> a -> Set AnyName
  , bindersD :: AlphaCtx -> a -> [AnyName]
  , freshenD :: forall m. Fresh m => AlphaCtx -> a -> m (a, Perm AnyName)
  , aeqD :: AlphaCtx -> a -> a -> Bool
  , isPatD :: a -> Maybe [AnyName]
  , isTermD :: a -> Bool
  , isEmbedD :: a -> Bool
  }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD swaps' swapall' fv' binders' freshen' aeq' isPat isTerm isEmbed

data AlphaCtx = Term | Pat deriving (Show, Eq, Read)

initial :: AlphaCtx
initial = Term

pat :: AlphaCtx -> AlphaCtx
pat c = Pat

term :: AlphaCtx -> AlphaCtx
term c = Term

mode :: AlphaCtx -> AlphaCtx
mode = id

class (Rep1 AlphaD a) => Alpha a where
  swaps' :: AlphaCtx -> Perm AnyName -> a -> a
  swaps' = swapsR1 rep1

  swapall' :: AlphaCtx -> Perm AnyName -> a -> a
  swapall' = swapallR1 rep1

  fv' :: AlphaCtx -> a -> Set AnyName
  fv' = fvR1 rep1

  binders' :: AlphaCtx -> a -> [AnyName]
  binders' = bindersR1 rep1

  freshen' :: Fresh m => AlphaCtx -> a -> m (a, Perm AnyName)
  freshen' = freshenR1 rep1

  aeq' :: AlphaCtx -> a -> a -> Bool
  aeq' = aeqR1 rep1

  isPat :: a -> Maybe [AnyName]
  isPat = isPatR1 rep1

  isTerm :: a -> Bool
  isTerm = isTermR1 rep1

  isEmbed :: a -> Bool
  isEmbed _ = False

class IsEmbed e where
  type Embedded e :: *

  -- |Construct an embedded term.
  embed :: Embedded e -> e

  -- |Destruct an embedded term.
  unembed :: e -> Embedded e

instance IsEmbed (Embed t) where
  type Embedded (Embed t) = t

  embed = Embed
  unembed (Embed t) = t

----------------------------------------------------
-- Specific Alpha Instances for binding combinators:
--   Name, Bind, Embed, Rec
----------------------------------------------------
instance Rep a => Alpha (Name a) where
  isTerm _ = True

  isPat n = Just [(AnyName n)]

  fv' Term n = S.singleton (AnyName n)
  fv' Pat  _ = S.empty

  binders' Term n = [AnyName n]
  binders' Pat  _ = []

  swaps' Term p x =
    case apply p (AnyName x) of
      AnyName y ->
        case gcastR (getR y) (getR x) y of
          Just y' -> y'
          Nothing -> error "Internal error in swaps': sort mismatch"
  swaps' Pat p x = x

  swapall' _ p x =
    case apply p (AnyName x) of
      AnyName y ->
        case gcastR (getR y) (getR x) y of
          Just y' -> y'
          Nothing -> error "Internal error in swapall': sort mismatch"

  aeq' c x y = x == y

  freshen' Term n = do
    x <- fresh n
    return (x, single (AnyName n) (AnyName x))
  freshen' Pat n = return (n, empty)

instance Alpha AnyName where
  isTerm _ = True

  isPat n = Just [n]

  fv' Term n = S.singleton n
  fv' Pat  _ = S.empty

  binders' Term n = [n]
  binders' Pat  _ = []

  swaps' Term p x = apply p x
  swaps' Pat p x = x

  swapall' _ p x = apply p x

  aeq' c x y = x == y

  freshen' Term (AnyName n) = do
    x <- fresh n
    return (AnyName x, single (AnyName n) (AnyName x))
  freshen' Pat n = return (n, empty)

instance (Alpha p, Alpha t) => Alpha (Bind p t) where
  isPat _ = Nothing

  isTerm (Bind p t) = isJust (isPat p) && isTerm t

  swaps' c pm (Bind p t) =
    Bind (swaps' Pat pm p) (swaps' c pm' t)
    where
      pm' = restrict pm (binders p)

  -- swapall' use default implementation.

  -- The free variables in a binder are the free variables in the
  -- binding pattern, plus the free variables in the bound term, minus
  -- the binders in the pattern.
  fv' c (Bind p t) =
    fv' Pat p `S.union` (fv' c t S.\\ (fv' Term p))

  -- The binders in a 'Bind' are the binders in the binding pattern
  -- plus the binders in the body, minus those from the pattern.
  binders' c (Bind p t) =
    binders' Pat p ++ (binders' c t L.\\ binders' Term p)

  aeq' c (Bind p1 t1) (Bind p2 t2)
    | bx1 == bx2 = aeq' c p1 p2 && aeq' c t1 t2
    | (S.fromList bx1) `S.intersection`
      (fv' Term t2 S.\\ fv' Term t1) /= S.empty = False
    | otherwise = aeq' c p1 (swaps' Term pm p2) &&
                  aeq' c t1 (swapall' Term pm t2)
    where bx1 = binders p1
          bx2 = binders p2
          pm  = foldl (<>) empty (zipWith single bx1 bx2)

  -- freshen' use default implementation.

instance (Alpha t) => Alpha (Embed t) where
  isPat (Embed t) = if isTerm t then Just [] else Nothing
  isTerm _ = False

  swaps' Pat perm (Embed t) = Embed (swaps' Term perm t)
  swaps' Term perm (Embed t) = Embed t

  -- swapall' uses default implementation

  fv' Pat (Embed t) = fv' Term t
  fv' Term (Embed t) = S.empty

  binders' Pat (Embed t) = binders' Term t
  binders' Term (Embed t) = []

  freshen' Pat (Embed t) = do
    (t', pm) <- freshen' Term t
    return (Embed t', pm)
  freshen' Term t = return (t, empty)

  -- aeq' uses default implementation

instance (Alpha p) => Alpha (Rec p) where
  isPat (Rec p) = isPat p
  isTerm _ = False

  swaps' Pat perm (Rec p) = Rec (swaps' Pat pm' p)
    where bx = binders' Pat p
          pm' = restrict perm bx
  swaps' _ _ p = p

  -- swapall' uses default implementation

  -- fv' uses default implementation

  binders' Pat (Rec p) = binders' Pat p
  binders' Term _ = []

  -- aeq' uses default implementation

  freshen' Pat (Rec p) = do
    (p', pm) <- freshen' Pat p
    return (Rec p', pm)
  freshen' Term t = return (t, empty)

------------------------------------
-- Generic Implementations
------------------------------------

-- |Generic swap.
swapsR1 :: R1 AlphaD a -> AlphaCtx -> Perm AnyName -> a -> a
swapsR1 (Data1 _ cons) = \ctx perm d ->
  case (findCon cons d) of
    Val c rec kids -> to c (map_l (\z -> swapsD z ctx perm) rec kids)
swapsR1 _ = \_ _ d -> d

swapallR1 :: R1 AlphaD a -> AlphaCtx -> Perm AnyName -> a -> a
swapallR1 (Data1 _ cons) = \ctx perm d ->
  case (findCon cons d) of
    Val c rec kids -> to c (map_l (\z -> swapallD z ctx perm) rec kids)
swapallR1 _ = \_ _ d -> d

-- |Generic free variable computation.
fvR1 :: R1 AlphaD a -> AlphaCtx -> a -> Set AnyName
fvR1 (Data1 _ cons) = \ctx d ->
  case (findCon cons d) of
    Val _ rec kids -> fv1 rec ctx kids
  where
    fv1 :: MTup (AlphaD) l -> AlphaCtx -> l -> Set AnyName
    fv1 MNil _ Nil = emptyC
    fv1 (r :+: rs) ctx (p1 :*: t1) =
      fvD r ctx p1 `S.union` fv1 rs ctx t1
fvR1 _ = \_ _ -> emptyC

-- |Generic binders.
bindersR1 :: R1 AlphaD a -> AlphaCtx -> a -> [AnyName]
bindersR1 (Data1 _ cons) = \ctx d ->
  case (findCon cons d) of
    Val _ rec kids -> bindersL rec ctx kids
bindersR1 _ = \_ _ -> []

bindersL :: MTup AlphaD l -> AlphaCtx -> l -> [AnyName]
bindersL MNil _ Nil = []
bindersL (r :+: rs) ctx (p :*: ps) =
  bindersD r ctx p ++ bindersL rs ctx ps

-- |Generic freshen.
freshenR1 :: Fresh m => R1 AlphaD a -> AlphaCtx -> a -> m (a, Perm AnyName)
freshenR1 (Data1 _ cons) = \ ctx d ->
  case (findCon cons d) of
    Val c rec kids -> do
      (l, perm) <- freshenL rec ctx kids
      return (to c l, perm)
freshenR1 _ = \_ n -> return (n, empty)

freshenL :: Fresh m => MTup AlphaD l -> AlphaCtx -> l -> m (l, Perm AnyName)
freshenL MNil _ Nil = return (Nil, empty)
freshenL (r :+: rs) ctx (t :*: ts) = do
  (xs, p2) <- freshenL rs ctx ts
  (x, p1) <- freshenD r ctx (swapsD r ctx p2 t)
  return (x :*: xs, p1 <> p2)

-- |Generic Alpha Equivalence.
aeqR1 :: R1 AlphaD a -> AlphaCtx -> a -> a -> Bool
aeqR1 (Data1 _ cons) = loop cons
  where
    loop (Con emb reps : rest) ctx x y =
      case (from emb x, from emb y) of
        (Just p1, Just p2) -> aeqL reps ctx p1 p2
        (Nothing, Nothing) -> loop rest ctx x y
        (_, _)             -> False
    loop [] _ _ _ = error "Impossible!"
aeqR1 Int1          = \_ x y -> x == y
aeqR1 Integer1      = \_ x y -> x == y
aeqR1 Char1         = \_ x y -> x == y
aeqR1 (Abstract1 _) = \_ x y -> error "Must override aeq' for abstract types"
aeqR1 _             = \_ _ _ -> False

aeqL :: MTup AlphaD l -> AlphaCtx -> l -> l -> Bool
aeqL MNil _ Nil Nil = True
aeqL (r :+: rs) c (p1 :*: t1) (p2 :*: t2) =
  aeqD r c p1 p2 && aeqL rs c t1 t2

-- |Generic dynamic check of whether a value is a valid pattern.
isPatR1 :: R1 AlphaD a -> a -> Maybe [AnyName]
isPatR1 (Data1 _ cons) = \d ->
  case (findCon cons d) of
    Val _ rec kids ->
      foldl_l (\c b a -> combine (isPatD c a) b) (Just []) rec kids
isPatR1 _ = \ _ -> Just []

combine :: Maybe [AnyName] -> Maybe [AnyName] -> Maybe [AnyName]
combine (Just ns1) (Just ns2) |
  ns1 `L.intersect` ns2 == [] = Just (ns1 ++ ns2)
combine _ _ = Nothing

-- |Generic dunamic check of whether a valud is a valid term.
isTermR1 :: R1 AlphaD a -> a -> Bool
isTermR1 (Data1 _ cons) = \d ->
  case findCon cons d of
    Val _ rec kids -> foldl_l (\c b a -> isTermD c a && b) True rec kids
isTermR1 _ = \_ -> True

-- Instances for other types use the default definitions.
instance Alpha Bool
instance Alpha Float
instance Alpha ()
instance Alpha a => Alpha [a]
instance Alpha Int
instance Alpha Integer
instance Alpha Double
instance Alpha Char
instance Alpha a => Alpha (Maybe a)
instance (Alpha a,Alpha b) => Alpha (Either a b)
instance (Alpha a,Alpha b) => Alpha (a,b)
instance (Alpha a,Alpha b,Alpha c) => Alpha (a,b,c)
instance (Alpha a, Alpha b,Alpha c, Alpha d) => Alpha (a,b,c,d)
instance (Alpha a, Alpha b,Alpha c, Alpha d, Alpha e) =>
   Alpha (a,b,c,d,e)

instance (Rep a) => Alpha (R a)

------------------------------------
-- Inline tests
------------------------------------
nameX :: N
nameX = s2n "x"

nameY :: N
nameY = s2n "y"

type N = Name Expr

data Expr = App Expr Expr
          | Abs (Bind N Expr)
          | Var N
          | Let (Bind (Rec [(N, Embed Expr)]) Expr) -- ^ recursive binding
          deriving (Show)

$(derive [''Expr])

-- Derive Alpha
instance Alpha Expr

-- Simple tests
xy  = App (Var nameX) (Var nameY)
xyAeqXy = aeq' Term xy xy
xy' = runFreshM $ freshen' Term xy
xyNAeqXy' = aeq' Term xy (fst xy')

fvXy = fv' Term xy
fvXy' = fv' Term (fst xy')

-- Simple Abs
idx = Abs (bind nameX (Var nameX))
idy = Abs (bind nameY (Var nameY))
idxAeqIdY = aeq idx idy
fvIdx = fv idx
bindersIdx = binders idx

-- Simple Let
yx = App (Var nameY) (Var nameX)
xEqY = (nameX, Embed $ Var nameY)
yEqX = (nameY, Embed $ Var nameX)
letBinders = [xEqY, yEqX]
letXY = Let (bind (Rec letBinders) yx)
bindersLet = binders' Pat letBinders
bindersLetXY = binders' Term letXY
fvLetXY = fv letXY

letYX = Let (bind (Rec $ reverse letBinders) xy)
