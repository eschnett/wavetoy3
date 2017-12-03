{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TLI where

import Data.Proxy
import qualified Data.Vector as V
import GHC.TypeLits



newtype NVector (n' :: Nat) a = NVector (V.Vector a)
    deriving (Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance KnownNat n' => Applicative (NVector n') where
    pure x = NVector (V.replicate n x)
        where n = fromInteger (natVal (Proxy :: Proxy n'))
    NVector fs <*> NVector xs = NVector (V.zipWith id fs xs)
