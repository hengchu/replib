{-# LANGUAGE RankNTypes
           , FlexibleContexts
           , GADTs
           , TypeFamilies
           , TemplateHaskell
           , FlexibleInstances
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}

module Unbound.Nominal.Alpha where

import Generics.RepLib hiding (GT)
import Unbound.PermM
import Unbound.Nominal.Name
import Unbound.Nominal.Types
import Unbound.Nominal.Fresh
import Unbound.Util

import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isJust)
import qualified Data.List as L
import Data.Monoid
import Control.Monad (liftM2)

------------------------------------
-- Public API
------------------------------------

-- |Smart constructor for binder.
bind :: (Alpha p, Alpha t) => p -> t -> Bind p t
bind = Bind

unbind :: (Alpha p, Alpha t, Fresh m) => Bind p t -> m (p, t)
unbind (Bind p t) = do
  (p', pm) <- freshen' Pat p
  return $ (p', (swapall' Term pm t))

rebind :: (Alpha p, Alpha q) => p -> q -> Rebind p q
rebind = Rebind

-- |List the binding variables in a pattern.
binders :: (Rep a, Alpha a) => a -> Set AnyName
binders = binders' initial

fv :: (Alpha a) => a -> Set AnyName
fv = fv' initial

aeq :: (Alpha a) => a -> a -> Bool
aeq = aeq' initial

match :: (Alpha a) => a -> a -> Maybe (Perm AnyName)
match = match' Pat

data AlphaD a = AlphaD {
  swapallD :: AlphaCtx -> Perm AnyName -> a -> a
  , matchD :: AlphaCtx -> a -> a -> Maybe (Perm AnyName)
  , fvD :: AlphaCtx -> a -> Set AnyName
  , bindersD :: AlphaCtx -> a -> Set AnyName
  , freshenD :: forall m. Fresh m => AlphaCtx -> a -> m (a, Perm AnyName)
  , aeqD :: AlphaCtx -> a -> a -> Bool
  , isPatD :: a -> Maybe [AnyName]
  , isTermD :: a -> Bool
  , isEmbedD :: a -> Bool
  }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD swapall' match' fv' binders' freshen' aeq' isPat isTerm isEmbed

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
  swapall' :: AlphaCtx -> Perm AnyName -> a -> a
  swapall' = swapallR1 rep1

  match' :: AlphaCtx -> a -> a -> Maybe (Perm AnyName)
  match' = matchR1 rep1

  fv' :: AlphaCtx -> a -> Set AnyName
  fv' = fvR1 rep1

  binders' :: AlphaCtx -> a -> Set AnyName
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

  binders' Term _ = S.empty
  binders' Pat  n = S.singleton $ AnyName n

  swapall' _ p x =
    case apply p (AnyName x) of
      AnyName y ->
        case gcastR (getR y) (getR x) y of
          Just y' -> y'
          Nothing -> error "Internal error in swapall': sort mismatch"

  aeq' c x y = x == y

  freshen' Pat n = do
    x <- fresh n
    return (x, single (AnyName n) (AnyName x))
  freshen' Term n = return (n, empty)

  match' Pat x y =
    if x == y then Just empty
              else Just $ single (AnyName x) (AnyName y)
  match' Term x y = Just empty

instance Alpha AnyName where
  isTerm _ = True

  isPat n = Just [n]

  fv' Term n = S.singleton n
  fv' Pat  _ = S.empty

  binders' Term _ = S.empty
  binders' Pat  n = S.singleton n

  swapall' _ p x = apply p x

  aeq' c x y = x == y

  freshen' Pat (AnyName n) = do
    x <- fresh n
    return (AnyName x, single (AnyName n) (AnyName x))
  freshen' Term n = return (n, empty)

  match' Pat x y =
    if x == y then Just empty
              else Just (single x y)
  match' Term x y = Just empty

instance (Ord a, Alpha a) =>  Alpha (Set a) where
  isTerm s = S.foldl' (&&) True (S.map isTerm s)

  isPat s = S.foldl' combine' (Just []) (S.map isPat s)
    where combine' = liftM2 (++)

  fv' c s = S.unions $ S.toList (S.map (fv' c) s)

  binders' c s = S.unions $ S.toList (S.map (binders' c) s)

  swapall' c p s = S.map (swapall' c p) s

  -- We can't match up element by element anyways.
  aeq' c s1 s2 = s1 == s2

  freshen' c s = do
    sp <- mapM (freshen' c) (S.toList s)
    let s' = S.fromList (map fst sp)
    let pm = foldl (<>) empty (map snd sp)
    return (s', pm)

instance (Alpha p, Alpha t) => Alpha (Bind p t) where
  isPat _ = Nothing

  isTerm (Bind p t) = isJust (isPat p) && isTerm t

  -- swapall' use default implementation.

  -- The free variables in a binder are the free variables in the
  -- binding pattern, plus the free variables in the bound term, minus
  -- the binders in the pattern.
  fv' c (Bind p t) =
    fv' Pat p `S.union` (fv' c t S.\\ (binders' Pat p))

  -- The binders in a 'Bind' are the binders in the binding pattern
  -- plus the binders in the body, minus the free variables in the
  -- pattern.
  binders' c (Bind p t) =
    binders' Pat p `S.union` (binders' c t S.\\ fv' Term p)

  aeq' c b1@(Bind p1 t1) b2@(Bind p2 t2) =
    case (match' Pat p1 p2) of
      Just pm -> fv b1 == fv b2 && aeq' c (swapall' c pm t1) t2
      Nothing -> False

  freshen' c (Bind p t) = do
    (p', pm1) <- freshen' Pat p
    (t', pm2) <- freshen' c (swapall' c pm1 t)
    return (Bind p' t', pm1 <> pm2)

  -- This seems to be the default implementation?
  match' c (Bind p1 t1) (Bind p2 t2) = do
    pm1 <- match' Pat p1 p2
    pm2 <- match' c t1 (swapall' c pm1 t2)
    return $ pm1 <> pm2

instance (Alpha t) => Alpha (Embed t) where
  isPat (Embed t) = if isTerm t then Just [] else Nothing
  isTerm _ = False

  -- swapall' uses default implementation

  fv' Pat (Embed t) = fv' Term t
  fv' Term (Embed t) = S.empty

  binders' Pat (Embed t) = binders' Term t
  binders' Term (Embed t) = S.empty

  freshen' Pat  p = return (p, empty)
  freshen' Term _ = error "freshen' called on a Embed in Term"

  aeq' c (Embed t1) (Embed t2) = aeq' Term t1 t2

  match' Pat (Embed x) (Embed y) = match' Term x y
  match' Term (Embed x) (Embed y) = error "match' called on a Embed in Term"

instance (Alpha p) => Alpha (Rec p) where
  isPat (Rec p) = isPat p
  isTerm _ = False

  -- swapall' uses default implementation

  fv' Pat (Rec p) = fv' Pat p S.\\ binders' Pat p
  fv' Term _      = S.empty

  binders' Pat (Rec p) = binders' Pat p
  binders' Term _ = S.empty

  freshen' Pat  (Rec p) = do
    let bx = binders' Pat p
    (bx', pm) <- freshen' Pat bx
    return (Rec (swapall' Pat pm p), pm)
  freshen' Term _ = error "freshen' called on Rec in Term mode"

  match' Pat (Rec x) (Rec y) = match' Pat x y
  match' Term (Rec x) (Rec y) = error "match' called on a Rec in Term"

  -- aeq' uses default implementation

instance (Alpha p1, Alpha p2) => Alpha (Rebind p1 p2) where
  isPat (Rebind p1 p2) =
    combine (isPat p1) (isPat p2)

  isTerm _ = False

  -- swapall' uses default implementation

  fv' Pat (Rebind p1 p2) =
    fv' Pat p1 `S.union` (fv' Pat p2 S.\\ binders' Pat p1)
  fv' Term _ = S.empty

  binders' Pat (Rebind p1 p2) =
    binders' Pat p1 `S.union` binders' Pat p2
  binders' Term _ = S.empty

  freshen' Pat (Rebind p1 p2) = do
    (p1', pm1) <- freshen' Pat p1
    (p2', pm2) <- freshen' Pat (swapall' Pat pm1 p2)
    return $ (Rebind p1' p2', pm1 <> pm2)
  freshen' Term (Rebind p1 p2) =
    error "freshen' called on Rebind in Term"

  match' Pat (Rebind p11 p12) (Rebind p21 p22) = do
    pm1 <- match' Pat p11 p21
    pm2 <- match' Pat p12 (swapall' Pat pm1 p22)
    return $ pm1 <> pm2
  match' Term _ _ = error "match' called on Rebind in Term"

  aeq' c l@(Rebind p1 q1) r@(Rebind p2 q2) =
    case (match' Pat p1 p2) of
      Just pm ->
        fv' Pat l == fv' Pat r && aeq' c q1 (swapall' c pm q2)
      Nothing -> False

------------------------------------
-- Generic Implementations
------------------------------------

-- |Generic swap.
swapallR1 :: R1 AlphaD a -> AlphaCtx -> Perm AnyName -> a -> a
swapallR1 (Data1 _ cons) = \ctx perm d ->
  case (findCon cons d) of
    Val c rec kids -> to c (map_l (\z -> swapallD z ctx perm) rec kids)
swapallR1 _ = \_ _ d -> d

-- |Generic match.
matchR1 :: R1 AlphaD a -> AlphaCtx -> a -> a -> Maybe (Perm AnyName)
matchR1 (Data1 _ cons) = loop cons where
  loop (Con emb reps:rest) c a1 a2 =
    case (from emb a1, from emb a2) of
      (Just as1, Just as2) -> matchL reps c as1 as2
      (Nothing, Nothing) -> loop rest c a1 a2
      (_, _) -> Nothing
  loop [] _ _ _ = error "Impossible: exhausted all constructors in matchR1"
matchR1 Int1 = \_ x y -> if x == y then Just empty else Nothing
matchR1 Integer1 = \_ x y -> if x == y then Just empty else Nothing
matchR1 Char1 = \_ x y -> if x == y then Just empty else Nothing
matchR1 _ = \_ _ _ -> Nothing

matchL :: MTup AlphaD l -> AlphaCtx -> l -> l -> Maybe (Perm AnyName)
matchL MNil _ Nil Nil = Just empty
matchL (r :+: rs) c (x :*: xs) (y :*: ys) = do
  l2 <- matchL rs c xs ys
  l1 <- matchD r c x (swapallD r c l2 y)
  return (l1 <> l2)

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
bindersR1 :: R1 AlphaD a -> AlphaCtx -> a -> Set AnyName
bindersR1 (Data1 _ cons) = \ctx d ->
  case (findCon cons d) of
    Val _ rec kids -> bindersL rec ctx kids
bindersR1 _ = \_ _ -> S.empty

bindersL :: MTup AlphaD l -> AlphaCtx -> l -> Set AnyName
bindersL MNil _ Nil = S.empty
bindersL (r :+: rs) ctx (p :*: ps) =
  bindersD r ctx p `S.union` bindersL rs ctx ps

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
  (x, p1) <- freshenD r ctx (swapallD r ctx p2 t)
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

nameZ :: N
nameZ = s2n "z"

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
zEqW = (nameZ, Embed $ Var (s2n "w"))
letBinders = [xEqY, yEqX]
letXY = Let (bind (Rec letBinders) yx)
bindersLet = binders' Pat letBinders
bindersLetXY = binders' Term letXY
fvLetXY = fv letXY

letYX = Let (bind (Rec $ reverse letBinders) xy)
letXYZ = Let (bind (Rec (letBinders ++ [zEqW])) xy)
absXY = Abs (bind nameX (App (Var nameX) (Var nameY)))

-------------------------------------------------
-- More testing code
-------------------------------------------------

data Exp = V (Name Exp)
         | A Exp Exp
         | L (Bind (Name Exp) Exp)
         deriving (Show)
$(derive [''Exp])

instance Alpha Exp

nameA, nameB, nameC :: Name Exp
nameA = s2n "A"
nameB = s2n "B"
nameC = s2n "C"

name1, name2, name3, name4 :: Name Exp
name1 = s2n "n1"
name2 = s2n "n2"
name3 = s2n "n3"
name4 = s2n "n4"

assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: IO ()
do_tests = do
  tests_aeq

naeq x y = not $ aeq x y
naeq' c x y = not $ aeq' c x y

naeqP :: (Alpha a) => a -> a -> Bool
naeqP = naeq' Pat

aeqP :: (Alpha a) => a -> a -> Bool
aeqP = aeq' Pat

a10a = bind (rebind (nameA, Embed nameC) ()) nameA
a10b = bind (rebind (nameB, Embed nameC) ()) nameB

a10c = bind (rebind (nameA, Embed nameA) ()) nameA
a10d = bind (rebind (nameB, Embed nameA) ()) nameB

tests_aeq :: IO ()
tests_aeq = do
  assert "a1" $ (bind nameA nameA) `naeq` (bind nameA nameB)
  assert "a2" $ (bind nameA nameA) `aeq` (bind nameA nameA)
  assert "a3" $ (bind nameA nameA) `aeq` (bind nameB nameB)
  assert "a4" $ (bind nameA nameB) `naeq` (bind nameB nameA)
  assert "a5" $ (bind (nameA, Embed nameB) nameA) `naeq`
                (bind (nameA, Embed nameC) nameA)
  assert "a6" $ (bind (nameA, Embed nameB) nameA) `aeq`
                (bind (nameA, Embed nameB) nameA)
  assert "a7" $ (bind (nameA, Embed nameB) nameA) `aeq`
                (bind (nameB, Embed nameB) nameB)
  assert "a8" $ rebind nameA nameB `naeqP` rebind nameB nameB
  assert "a9" $ rebind nameA nameA `aeqP` rebind nameA nameA
  assert "a9a" $ (bind (rebind nameA (Embed nameA)) nameA) `aeq`
                 (bind (rebind nameB (Embed nameB)) nameB)
  assert "a10" $ bind (rebind (nameA, Embed nameA) ()) nameA `aeq`
                 bind (rebind (nameB, Embed nameA) ()) nameB
  assert "a10a" $ a10a `aeq` a10b
  assert "a11" $ bind (rebind (nameA, Embed nameA) ()) nameA `naeq`
                 bind (rebind (nameB, Embed nameB) ()) nameB
  assert "a12" $ bind (Embed nameA) () `naeq` bind (Embed nameB) ()
  assert "a13" $ bind (Embed nameA) () `aeq` bind (Embed nameA) ()
  assert "a14" $ bind (rebind (Embed nameA) ()) () `naeq`
                 bind (rebind (Embed nameB) ()) ()
  assert "a15" $ (rebind (nameA, Embed nameA) ()) `naeq`
                 (rebind (name4, Embed nameC) ())
  assert "a16" $ bind (nameA, nameB) nameA `naeq`
                 bind (nameB, nameA) nameA
  assert "a17" $ bind (nameA, nameB) nameA `naeq` bind (nameA, nameB) nameB
  assert "a18" $ (nameA, nameA) `naeq` (nameA, nameB)
  assert "a19" $ match (nameA, nameA) (nameB, nameC) == Nothing
  assert "a20" $ (L (bind name2
                     (L (bind name3
                         (L (bind name4
                             (A (V name2)
                              (A (V name3)
                               (V name4))))))))) `aeq`
                  (L (bind name1
                      (L (bind name2
                          (L (bind name3
                              (A (V name1)
                               (A (V name2)
                                (V name3)))))))))
