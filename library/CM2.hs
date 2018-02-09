{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module CM2 where

import Control.Comonad
import Control.Comonad.Store
import Data.Functor.Compose



-- | This instance is probably not lawful.
-- Could also use Distributive instead of Traversable.
instance (Comonad v, Traversable v, Comonad w, Applicative w)
    => Comonad (Compose v w) where
    extract (Compose w) = extract (extract w)
    -- extend f (Compose w) = Compose _
    --     where f' w = f (Compose w)
    duplicate (Compose w) =
        Compose $ fmap (fmap Compose) $ fmap sequenceA $ duplicate $ fmap duplicate $ w

instance (Comonad v, ComonadStore s v, Comonad w, ComonadStore t w
         , Comonad (Compose v w))
    => ComonadStore (s, t) (Compose v w) where
    pos (Compose w) = (pos w, pos (extract w))
    peek (s, t) (Compose w) = peek t (peek s w)
    seek (s, t) (Compose w) = Compose (fmap (seek t) (seek s w))
