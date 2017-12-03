{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module EfficientVector where

import Data.Kind
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
-- import IfCxt



newtype Vector a = Vector
  { getImpl :: Impl a
  }

type Impl a = Impl' a a

type family Impl' a where
  Impl' () = U.Vector
  Impl' Int = U.Vector
  Impl' Float = U.Vector
  Impl' Double = U.Vector
  Impl' (a, b) = Prod (Impl' a) (Impl' b)
  Impl' (a, b, c) = Prod (Impl' (a, b)) (Impl' c)
  Impl' (a, b, c, d) = Prod (Impl' (a, b, c)) (Impl' d)
  Impl' _ = V.Vector

type family Prod a b where
  Prod U.Vector U.Vector = U.Vector
  Prod _ _ = V.Vector

type family Constr impl a where
  Constr U.Vector a = U.Unbox a
  Constr V.Vector _ = (() :: Constraint)

deriving instance Eq (Impl a) => Eq (Vector a)

deriving instance Ord (Impl a) => Ord (Vector a)

deriving instance Read (Impl a) => Read (Vector a)

deriving instance Show (Impl a) => Show (Vector a)

u2v :: U.Unbox a => U.Vector a -> V.Vector a
-- u2v xs = V.generate (U.length xs) (xs U.!)
u2v = fmapuv id

v2u :: U.Unbox a => V.Vector a -> U.Vector a
-- v2u xs = U.generate (V.length xs) (xs V.!)
v2u = fmapvu id

fmapuu :: (U.Unbox a, U.Unbox b) => (a -> b) -> U.Vector a -> U.Vector b
fmapuu = G.map

fmapvv :: (a -> b) -> V.Vector a -> V.Vector b
fmapvv = G.map

fmapuv :: U.Unbox a => (a -> b) -> U.Vector a -> V.Vector b
-- fmapuv f = fmapvv f . u2v
fmapuv f xs = G.generate (G.length xs) (f . (xs G.!))

fmapvu :: U.Unbox b => (a -> b) -> V.Vector a -> U.Vector b
-- fmapvu f = v2u . fmapvv f
fmapvu f xs = G.generate (G.length xs) (f . (xs G.!))
 -- fmapuu :: (U.Unbox a, U.Unbox b, Impl' a ~ U.Vector, Impl' b ~ U.Vector) =>
--           (a -> b) -> Vector a -> Vector b
-- fmapuu f (Vector xs) = Vector (U.map f xs)
-- 
-- fmapvv :: (Impl' a ~ V.Vector, Impl' b ~ V.Vector) =>
--           (a -> b) -> Vector a -> Vector b
-- fmapvv f (Vector xs) = Vector (V.map f xs)
-- 
-- fmapuv :: (U.Unbox a, Impl' a ~ U.Vector, Impl' b ~ V.Vector) =>
--           (a -> b) -> Vector a -> Vector b
-- fmapuv f = fmapvv f . Vector . u2v . getImpl
-- 
-- fmapvu :: (U.Unbox b, Impl' a ~ V.Vector, Impl' b ~ U.Vector) =>
--           (a -> b) -> Vector a -> Vector b
-- fmapvu f (Vector xs) = Vector (U.generate (V.length xs) (\i -> f (xs V.! i)))
-- instance Functor Vector where
--     fmap f = G.map f
