{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module PLC1 (PLC1(..)) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Store
import Control.Exception (assert)
-- import Control.Monad
-- import Data.Distributive
import Data.Proxy
import Data.Unfoldable
import Data.Validity
import qualified Data.Vector as V
import Data.VectorSpace
import GHC.TypeLits
-- import Linear.Metric
-- import Linear.Vector
import qualified Numeric.LinearAlgebra as L
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Function as QC

import ComonadicVector
import Function
import Integration



-- https://hackage.haskell.org/package/polynomial-0.7.3

newtype PLC1 (n' :: Nat) c s = PLC1
  { getPLC1 :: ComonadicVector V.Vector s
  } deriving (Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance (KnownNat n', Validity s) => Validity (PLC1 n' c s) where
    validate (PLC1 xs) =
        mconcat
        [ n > 0 <?@> "length is positive"
        , length xs == n <?@> "vector has correct length "
        , xs <?!> "vector"
        ]
        where n = fromInteger (natVal (Proxy :: Proxy n'))
    isValid = isValidByValidating

instance KnownNat n' => Unfoldable (PLC1 n' c) where
    -- unfold xs = PLC1 <$> unfold xs
    -- unfold xs = (PLC1 . ComonadicVector 0 . V.fromListN n) <$> mklist n
    --     where n = fromInteger (natVal (Proxy :: Proxy n')) :: Int
    --           mklist i | i == 0 = pure []
    --                    | otherwise = (:) <$> xs <*> mklist (i-1)
    unfold xs = PLC1 . goodlength <$> unfold xs
        where n = fromInteger (natVal (Proxy :: Proxy n')) :: Int
              goodlength ys = assert (n > 0 && length ys == n) ys

instance (Applicative (ComonadicVector V.Vector), KnownNat n') =>
         Applicative (PLC1 n' c) where
  -- pure x = PLC1 (pure x)
  -- Note: 'pure' should use the neutral element of the monoid used
  -- for 'pos_' in '(<*>)'
  pure x = PLC1 (ComonadicVector (n - 1) (V.replicate n x))
      where n = fromInteger (natVal (Proxy :: Proxy n'))
  PLC1 fs <*> PLC1 xs = PLC1 (fs <*> xs)

-- instance (Alternative (ComonadicVector V.Vector), KnownNat n') =>
--          Alternative (PLC1 n' c) where
--   empty = PLC1 empty
--   PLC1 xs <|> PLC1 ys = PLC1 (xs <|> ys)

-- instance Monad (ComonadicVector V.Vector) => Monad (PLC1 n' c) where
--     -- (>>=) :: PLC1 n' c s -> (s -> PLC1 n' c t) -> PLC1 n' c t
--     PLC1 x >>= f = PLC1 (x >>= getPLC1 . f)
-- 
-- instance MonadPlus (ComonadicVector V.Vector) => MonadPlus (PLC1 n' c) where
--     mzero = PLC1 mzero
--     PLC1 xs `mplus` PLC1 ys = PLC1 (xs `mplus` ys)

-- instance Distributive (ComonadicVector V.Vector) =>
--          Distributive (PLC1 n' c) where
--   collect f arr = PLC1 (collect (getPLC1 . f) arr)

instance Comonad (ComonadicVector V.Vector) => Comonad (PLC1 n' c) where
  extract (PLC1 arr) = extract arr
  extend f (PLC1 arr) = PLC1 (extend (f . PLC1) arr)

instance ComonadStore Int (ComonadicVector V.Vector) =>
         ComonadStore Int (PLC1 n' c) where
  pos (PLC1 arr) = pos arr
  peek i (PLC1 arr) = peek i arr



instance (KnownNat n', QC.Arbitrary s) => QC.Arbitrary (PLC1 n' c s) where
  -- arbitrary = do
  --   arr <- QC.arbitrary
  --   return (PLC1 arr)
  -- shrink (PLC1 arr) = [PLC1 arr' | arr' <- QC.shrink arr]
  -- arbitrary = arbitraryDefault
  arbitrary = do
      xs <- V.generateM n (const QC.arbitrary)
      i <- QC.choose (0, V.length xs - 1)
      return (PLC1 (ComonadicVector i xs))
      where n = fromInteger (natVal (Proxy :: Proxy n'))
  shrink arr = [arr' | pos arr > 0] ++ traverse QC.shrink arr'
      where arr' = seek 0 arr

instance QC.CoArbitrary s => QC.CoArbitrary (PLC1 n' c s) where
    coarbitrary = QC.coarbitrary . getPLC1

instance QC.Function s => QC.Function (PLC1 n' c s) where
    function = QC.functionMap getPLC1 PLC1



-- instance Additive (ComonadicVector V.Vector) => Additive (PLC1 n' c) where
--     zero = PLC1 zero
-- 
-- instance (Additive (PLC1 n' c), Bounded c, RealFrac c) => Metric (PLC1 n' c) where
--     -- dot :: Num a => f a -> f a -> a
--     dot xs ys =
--         assert (length ys == n) $
--         case n of
--           0 -> 0
--           _ -> sum [w i * peek i xs * peek i ys | i <- [0 .. n-1]]
--         where n = length xs
--               xmin = minBound :: c
--               xmax = maxBound :: c
--               w i = realToFrac (weight n xmin xmax i)

instance ( KnownNat n'
         , AdditiveGroup (ComonadicVector V.Vector s)
         , AdditiveGroup s
         ) =>
         AdditiveGroup (PLC1 n' c s) where
  zeroV = pure zeroV
  negateV = fmap negateV
  (^+^) = liftA2 (^+^)

instance ( KnownNat n'
         , VectorSpace (ComonadicVector V.Vector s)
         , VectorSpace s
         ) =>
         VectorSpace (PLC1 n' c s) where
  type Scalar (PLC1 n' c s) = Scalar s
  (*^) x = fmap (x *^)

-- instance ( KnownNat n'
--          , Bounded c
--          , RealFrac c
--          , InnerSpace s
--          , VectorSpace (Scalar s)
--          , Fractional (Scalar (Scalar s))
--          ) =>
--          InnerSpace (PLC1 n' c s) where
--   -- xs <.> ys =
--   --   assert (length ys == length xs) $ sumV (weighted ((<.>) <$> xs <*> ys))

instance ( KnownNat n'
         , Integrable (PLC1 n')
         , IntegrableOk (PLC1 n') c s
         , Bounded c
         , RealFrac c
         , InnerSpace s
         , Fractional (Scalar s)
         ) => InnerSpace (PLC1 n' c s) where
  xs <.> ys = getPLC1 (extend weighted xs) <.> getPLC1 ys
    where
      weighted zs = weight n (xmin, xmax) (pos zs) *^ extract zs
      -- n = length xs
      n = fromInteger (natVal (Proxy :: Proxy n'))
      (xmin, xmax) = bounds xs



instance Function (PLC1 n') where
  type FunctionOk (PLC1 n') a b = ( KnownNat n'
                                  , Bounded a
                                  , RealFrac a
                                  , InnerSpace b
                                  , Floating (Scalar b)
                                  , Ord (Scalar b)
                                  , b ~ Double) -- TODO
  eval (PLC1 arr) x =
    case n of
      0 -> zeroV
      1 -> extract arr
      _ ->
        let y = ((x - cx) / rx + 1) / 2 * fromIntegral (n - 1)
            i = max 0 $ min (n - 2) $ floor y
            f0 = 1 - f1
            f1 = realToFrac (y - fromIntegral i)
        in f0 *^ peek i arr ^+^ f1 *^ peek (i + 1) arr
    where
      -- n = length arr
      n = fromInteger (natVal (Proxy :: Proxy n'))
      xmin = minBound `asTypeOf` x
      xmax = maxBound `asTypeOf` x
      cx = (xmax + xmin) / 2
      rx = (xmax - xmin) / 2

instance KnownNat n' => Discretization (PLC1 n') where
  discretized f = PLC1 (ComonadicVector 0 res)
    where
      n = fromInteger (natVal (Proxy :: Proxy n'))
      -- res = V.generate n go
      -- TODO: use (symmetric) triangular solver
      rhs = L.vector [go i | i <- [0..n-1]]
      mat = L.matrix n [ overlap n (xmin, xmax) i j
                       | i <- [0..n-1], j <- [0..n-1]]
      res = V.fromListN n $ L.toList $ mat L.<\> rhs
      (xmin, xmax) = (minBound, maxBound)
      _ = (f xmin, f xmax)      -- constrain types
      go i = integrate bf lo hi
        where
          bf x = b x *^ f x
          b x = basis n (xmin, xmax) i x
          (lo, hi) = support n (xmin, xmax) i

instance KnownNat n' => Integrable (PLC1 n') where
  type IntegrableOk (PLC1 n') a b = ()
  integral xs = sumV (extend weighted xs)
    where
      weighted ys = weight n (xmin, xmax) (pos ys) *^ extract ys
      -- n = length xs
      n = fromInteger (natVal (Proxy :: Proxy n'))
      (xmin, xmax) = bounds xs

instance Differentiable (PLC1 n') where
  type DifferentiableOk (PLC1 n') a b = ()
  type Dir (PLC1 n') = ()
  boundary () xs = extend bndry xs
    where
      bndry ys
        | n == 1     = zeroV *^ extract ys -- or zeroV
        | i == 0     = negateV (extract ys ^/ realToFrac dx)
        | i == n - 1 = extract ys ^/ realToFrac dx
        | otherwise  = zeroV *^ extract ys -- or zeroV
        where
          i = pos ys
      -- n = length xs
      n = fromInteger (natVal (Proxy :: Proxy n'))
      (xmin, xmax) = bounds xs
      rx = (xmax - xmin) / 2
      hdx = rx / fromIntegral (n - 1)
      dx = 2 * hdx
  derivative () xs = extend deriv xs
    where
      deriv ys
        | n == 1     = zeroV *^ extract ys -- or zeroV
        | i == 0     = (peek (i + 1) ys ^-^ extract ys) ^/ realToFrac dx
        | i == n - 1 = (extract ys ^-^ peek (i - 1) ys) ^/ realToFrac dx
        | otherwise  =
            (peek (i + 1) ys ^-^ peek (i - 1) ys) ^/ realToFrac (2 * dx)
        where
          i = pos ys
      -- n = length xs
      n = fromInteger (natVal (Proxy :: Proxy n'))
      (xmin, xmax) = bounds xs
      rx = (xmax - xmin) / 2
      hdx = rx / fromIntegral (n - 1)
      dx = 2 * hdx

triangle :: (Num a, Ord a) => a -> a
triangle x = max 0 (1 - abs x)

typed :: f a b -> a -> a
typed _ = id

bounds :: Bounded a => f a b -> (a, a)
bounds xs = (typed xs minBound, typed xs maxBound)

-- The basis functions are defined to have a maximum of '1'
basis :: (RealFrac a, Fractional b) => Int -> (a, a) -> Int -> a -> b
basis n (xmin, xmax) i x | n == 1    = 1
                         | otherwise = realToFrac (triangle y)
  where
    cx  = (xmin + xmax) / 2
    rx  = (xmax - xmin) / 2
    hdx = rx / fromIntegral (n - 1)
    xi  = cx + hdx * fromIntegral (2 * i + 1 - n)
    dx  = 2 * hdx
    y   = (x - xi) / dx

support :: (Fractional a, Ord a) => Int -> (a, a) -> Int -> (a, a)
support n (xmin, xmax) i | n == 1    = (xmin, xmax)
                         | otherwise = (max xmin (xi - dx), min xmax (xi + dx))
  where
    cx  = (xmin + xmax) / 2
    rx  = (xmax - xmin) / 2
    hdx = rx / fromIntegral (n - 1)
    xi  = cx + hdx * fromIntegral (2 * i + 1 - n)
    dx  = 2 * hdx

-- Volume
weight :: (RealFrac a, Fractional b) => Int -> (a, a) -> Int -> b
weight n (xmin, xmax) i | n == 1     = realToFrac (2 * rx)
                        | i == 0     = realToFrac hdx
                        | i == n - 1 = realToFrac hdx
                        | otherwise  = realToFrac (2 * hdx)
  where
    rx  = (xmax - xmin) / 2
    hdx = rx / fromIntegral (n - 1)

overlap :: (RealFrac a, Fractional b) => Int -> (a, a) -> Int -> Int -> b
overlap n (xmin, xmax) i j
    | n == 1                           = realToFrac (2 * rx)
    | i == j && (i == 0 || i == n - 1) = realToFrac (2 / 3 * hdx)
    | i == j                           = realToFrac (4 / 3 * hdx)
    | abs (i - j) == 1                 = realToFrac (1 / 3 * hdx)
    | otherwise                        = 0
  where
    rx  = (xmax - xmin) / 2
    hdx = rx / fromIntegral (n - 1)
