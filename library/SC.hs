{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SC where

import Control.Comonad
import Control.Comonad.Store
import qualified Data.Vector as V



mkStore :: V.Vector a -> Store Int a
mkStore xs = store (xs V.!) 0

-- extract' :: Comonad w => w a -> a
extract' :: Store p a -> a
extract' s = extract s

extend' :: (Store p a -> b) -> Store p a -> Store p b
extend' f s = extend f s

duplicate' :: Store p a -> Store p (Store p a)
duplicate' s = duplicate s

pos' :: Store p a -> p
pos' s = pos s



data Store' s a = Store' (s -> a) s

instance Functor (Store' s) where
    fmap f (Store' wf wp) = Store' (f . wf) wp

instance Comonad (Store' s) where
    extract (Store' wf wp) = wf wp
    extend f (Store' wf wp) = Store' (\wp' -> f (Store' wf wp')) wp
    -- duplicate (Store' wf wp) = Store' (\wp' -> Store' wf wp') wp

instance ComonadStore s (Store' s) where
    pos (Store' _ wp) = wp
    peek p (Store' wf _) = wf p
