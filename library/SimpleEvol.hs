{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}

{-# OPTIONS_GHC -Wno-type-defaults #-}

module SimpleEvol (initial, rhs, rk2, norm2) where

import Control.Exception (assert)
-- import Control.Monad.State.Strict
import qualified Data.Vector.Unboxed as U

default (Int, Double)



n :: Int
n = 100

type E = Double

ni :: Int
ni = n
nj :: Int
nj = n
nk :: Int
nk = n

np :: Int
np = ni * nj * nk

dx :: E
dx = 1 / fromIntegral ni
dy :: E
dy = 1 / fromIntegral nj
dz :: E
dz = 1 / fromIntegral nk

dt :: E
dt = minimum [dx, dy, dz] / 2

newtype GridFunc3 a = GridFunc3 (U.Vector a)
    deriving (Eq, Ord, Read, Show)

ind3 :: Int -> Int -> Int -> Int
ind3 i j k = assert
    (0 <= i && i < ni && 0 <= j && j < nj && 0 <= k && k < nk)
    (i + ni * j + ni * nj * k)

at3 :: U.Unbox a => Int -> Int -> Int -> GridFunc3 a -> a
at3 i j k (GridFunc3 u) = u U.! ind3 i j k
{-# INLINE at3 #-}

replicate3 :: U.Unbox a => a -> GridFunc3 a
replicate3 x = GridFunc3 (U.replicate np x)

-- imap3
--     :: (U.Unbox a, U.Unbox b)
--     => (Int -> Int -> Int -> a -> b)
--     -> GridFunc3 a
--     -> GridFunc3 b
-- imap3 f u = GridFunc3
--     ( U.fromListN
--         np
--         [ f i j k (at3 i j k u)
--         | i <- [0 .. ni - 1]
--         , j <- [0 .. nj - 1]
--         , k <- [0 .. nk - 1]
--         ]
--     )
-- {-# INLINE imap3 #-}

imap3
    :: (U.Unbox a, U.Unbox b)
    => (Int -> Int -> Int -> a -> b)
    -> GridFunc3 a
    -> GridFunc3 b
imap3 f (GridFunc3 u) = GridFunc3 (U.imap f' u)
  where
    f' ijk =
        let (jk, i) = ijk `divMod` ni
            (k , j) = jk `divMod` nj
        in  f i j k
{-# INLINE imap3 #-}

-- data Idx3 = Idx3 !Int !Int !Int
--             deriving (Eq, Ord, Read, Show)
-- 
-- start :: Idx3
-- start = Idx3 0 0 0
-- 
-- next :: Idx3 -> Idx3
-- next !(Idx3 i j k) | i < ni    = Idx3 (i + 1) j k
--                    | j < nj    = Idx3 0 (j + 1) k
--                    | otherwise = Idx3 0 0 (k + 1)
-- 
-- imap3
--     :: (U.Unbox a, U.Unbox b)
--     => (Int -> Int -> Int -> a -> b)
--     -> GridFunc3 a
--     -> GridFunc3 b
-- imap3 f (GridFunc3 u) = GridFunc3 (evalState (U.mapM mf u) start)
--   where
--     -- f' :: Idx3 -> a -> b
--     f' !(Idx3 i j k) x = f i j k x
--     {-# INLINE f' #-}
--     -- mf :: (U.Unbox a, U.Unbox b) => a -> Idx3S b
--     mf x = do
--         idx <- get
--         let r = f' idx x
--         modify' next
--         return r
--     {-# INLINE mf #-}
-- {-# INLINE imap3 #-}



foldl3' :: U.Unbox b => (a -> b -> a) -> a -> GridFunc3 b -> a
foldl3' f z (GridFunc3 u) = U.foldl' f z u



axpy :: (Num a, U.Unbox a) => a -> GridFunc3 a -> GridFunc3 a -> GridFunc3 a
axpy a (GridFunc3 x) (GridFunc3 y) = GridFunc3 (U.zipWith axpy' x y)
    where axpy' x' y' = a * x' + y'
-- {-# INLINE axpy #-}

-- axpy :: (Num a, U.Unbox a) => a -> GridFunc3 a -> GridFunc3 a -> GridFunc3 a
-- axpy a (GridFunc3 x) (GridFunc3 y) = GridFunc3 (U.imap axpy' x)
--     where axpy' i x' = a * x' + (y U.! i)
-- {-# INLINE axpy #-}



initial :: E -> GridFunc3 E
initial x = replicate3 x

-- Algorithm:
--    14 Flop/point
--    16 Byte/point
-- CPU:
--    180 ps/Flop   (2.8 GHz, assuming single core, no AVX, no FMA)
--    39 ps/Byte   (1.6 GHz DDR3, 2 transfers/cycle, 64 bit/transfer,
--                  dual-channel)
-- Theoretical:
--    2.5 ns/point
--    0.62 ns/point
--    2.5 ms/RHS
rhs :: GridFunc3 E -> GridFunc3 E
rhs u = imap3 lap3 u
  where
    lap3 i j k u0
        | (i == 0)
            || (i == ni - 1)
            || (j == 0)
            || (j == nj - 1)
            || (k == 0)
            || (k == nk - 1)
        = 0
        | otherwise
        = ((at3 (i - 1) j k u - 2 * u0 + at3 (i + 1) j k u) / dx ^ 2)
            + ((at3 i (j - 1) k u - 2 * u0 + at3 i (j + 1) k u) / dy ^ 2)
            + ((at3 i j (k - 1) u - 2 * u0 + at3 i j (k + 1) u) / dz ^ 2)
    {-# INLINE lap3 #-}
-- {-# INLINE rhs #-}

rk2 :: GridFunc3 E -> GridFunc3 E
rk2 u0 =
    let r0 = rhs u0
        u1 = axpy (0.5 * dt) r0 u0
        r1 = rhs u1
        u2 = axpy dt r1 u0
        -- {-# INLINE r0 #-}
        -- {-# INLINE r1 #-}
    in  u2

-- rk2 :: GridFunc3 E -> GridFunc3 E
-- rk2 u0 =
--     let u1 = axpy (0.5 * dt) (rhs u0) u0
--         u2 = axpy dt (rhs u1) u0
--     in  u2

norm2 :: (U.Unbox a, Floating a) => GridFunc3 a -> a
norm2 u = un2 (foldl3' n2 0 u)
  where
    n2 s x = s + x ^ 2
    un2 x = sqrt (x / fromIntegral np)
