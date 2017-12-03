{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MonadComprehensions #-}

module Poly
    ( Poly(..)
    , evalPoly
    , intPoly
    ) where

import GHC.Generics
import Data.List.Index (imap)
import qualified Test.QuickCheck as QC



newtype Poly a = Poly { polyCoeffs :: [a] }
    deriving (Eq, Ord, Read, Show, Generic)

evalPoly :: Num a => Poly a -> a -> a
evalPoly (Poly cs) x = foldr (\c s -> c + x * s) 0 cs

intPoly :: Fractional a => Poly a -> Poly a
intPoly (Poly cs) = Poly $ 0 : imap intcoeff cs
    where intcoeff i c = c / fromIntegral (i + 1)

instance QC.Arbitrary a => QC.Arbitrary (Poly a) where
    arbitrary = QC.scale (max 5) [Poly xs | xs <- QC.arbitrary]
    shrink = QC.genericShrink
