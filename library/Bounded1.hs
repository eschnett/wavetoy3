{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Provide bounded types, i.e. types with values restricted to a
-- certain interval
module Bounded1 (Bounded1(..)) where

import Control.Applicative
import Data.VectorSpace
import Numeric.IEEE
import qualified Test.QuickCheck as QC



-- | A bounded value, living in the interval @[-1; 1]@
newtype Bounded1 a = Bounded1 { getBounded1 :: a }
    deriving (Eq, Ord, Read, Show,
              IEEE,
              Foldable, Functor, Traversable,
              Fractional, Num, Real, RealFrac, Floating, RealFloat,
              AdditiveGroup,
              QC.CoArbitrary)

instance Applicative Bounded1 where
    pure = Bounded1
    Bounded1 f <*> Bounded1 x = Bounded1 (f x)

instance VectorSpace a => VectorSpace (Bounded1 a) where
    type Scalar (Bounded1 a) = Bounded1 (Scalar a)
    (*^) = liftA2 (*^)

instance InnerSpace a => InnerSpace (Bounded1 a) where
    (<.>) = liftA2 (<.>)

instance (QC.Arbitrary a, Bounded (Bounded1 a), RealFrac a) =>
         QC.Arbitrary (Bounded1 a) where
    arbitrary = QC.sized $ \size' ->
                do let size = toInteger size'
                   q <- QC.choose (- (size + 1), size + 1)
                   let (mn, mx) = (minBound, maxBound)
                   let r = (mx - mn) / 2 :: Bounded1 a
                   let m = (mn + mx) / 2
                   let x = fromIntegral q / fromIntegral (size + 1) * r - m
                   return x
    shrink (Bounded1 x) = [Bounded1 x' | x' <- QC.shrink x]

instance (Num a, Ord a) => Bounded (Bounded1 a) where
    minBound = -1
    maxBound = 1
