{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Split where

import qualified Data.Vector as V
-- import qualified Data.Vector.Generic as G
-- import qualified Data.Vector.Storable as S
import qualified Data.Vector.Unboxed as U



--------------------------------------------------------------------------------



type family VectorImpl a where
    VectorImpl Int = U.Vector Int
    VectorImpl a = V.Vector a



data VectorInstances = VectorInstances
    { foldMap1 :: !(forall m a . Monoid m => (a -> m) -> VectorImpl a -> m)
    , fmap1 :: !(forall a b . (a -> b) -> VectorImpl a -> VectorImpl b)
    }

ufoldMap :: (U.Unbox a, Monoid m) => (a -> m) -> U.Vector a -> m
ufoldMap f = U.foldl' (\r x -> r `mappend` f x) mempty

vfoldMap :: Monoid m => (a -> m) -> V.Vector a -> m
vfoldMap = foldMap

uufmap :: (U.Unbox a, U.Unbox b) => (a -> b) -> U.Vector a -> U.Vector b
uufmap = U.map

uvfmap :: U.Unbox a => (a -> b) -> U.Vector a -> V.Vector b
uvfmap f xs = V.generate (U.length xs) (\i -> f (xs U.! i))

vufmap :: U.Unbox b => (a -> b) -> V.Vector a -> U.Vector b
vufmap f xs = U.generate (V.length xs) (\i -> f (xs V.! i))

vvfmap :: (a -> b) -> V.Vector a -> V.Vector b
vvfmap = fmap



newtype Vector a = Vector { getVector :: VectorImpl a }

deriving instance Eq (VectorImpl a) => Eq (Vector a)
deriving instance Ord (VectorImpl a) => Ord (Vector a)
deriving instance Read (VectorImpl a) => Read (Vector a)
deriving instance Show (VectorImpl a) => Show (Vector a)

-- instance Foldable Vector where
--     foldMap f (Vector xs) = foldMap1 f xs
-- 
-- instance Functor Vector where
--     fmap f (Vector xs) = Vector (fmap1 f xs)








-- instance Foldable (Vector V.Vector) where
--     foldMap f = foldMap f . getVector
-- 
-- instance Functor (Vector V.Vector) where
--     fmap f = Vector . fmap f . getVector
-- 
-- 
-- 
-- class Foldable0 fa where
--     type Cont fa :: Type -> Type
--     type Elem fa :: Type
--     foldMap0 :: Monoid m => (Elem fa -> m) -> fa -> m
-- 
-- instance Foldable f => Foldable0 (f a) where
--     type Cont (f a) = f
--     type Elem (f a) = a
--     foldMap0 = foldMap
-- 
-- instance U.Unbox a => Foldable0 (U.Vector a) where
--     type Cont (U.Vector a) = U.Vector
--     type Elem (U.Vector a) = a
--     foldMap0 f = U.foldl' (\r -> mappend r . f) mempty
