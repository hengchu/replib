module Unbound.Nominal.Ops where

import Unbound.Nominal.Types
import Unbound.Nominal.Types

rec :: p -> Rec p
rec = Rec

unrec :: Rec p -> p
unrec (Rec p) = p

unembed :: Embed t -> t
unembed (Embed t) = t

embed :: t -> Embed t
embed = Embed
