{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Subcategory1 where

import Data.Functor.Identity
import Data.Functor.Product
import Data.Kind
import qualified Data.Vector.Unboxed as U
import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , (<$>)
                      , Applicative(..)
                      , Traversable(..)
                      )



type family CategoryOk (f :: Type -> Type) a :: Constraint

type FunctorOk (f :: Type -> Type) a =
    ((CategoryOk f a, ThisFunctorOk f a) :: Constraint)

class Functor f where
    type ThisFunctorOk (f :: Type -> Type) a :: Constraint
    type ThisFunctorOk f a = ()
    fmap :: (FunctorOk f a, FunctorOk f b) => (a -> b) -> f a -> f b

type ApplyOk (f :: Type -> Type) a =
    ((FunctorOk f a, ThisApplyOk f a) :: Constraint)

class Functor f => Apply f where
    type ThisApplyOk (f :: Type -> Type) a :: Constraint
    type ThisApplyOk f a = ()
    liftF1 :: (ApplyOk f a, ApplyOk f b) => (a -> b) -> f a -> f b
    liftF1 = fmap
    liftF2 :: (ApplyOk f a, ApplyOk f b, ApplyOk f c)
              => (a -> b -> c) -> f a -> f b -> f c



type instance CategoryOk Identity a = ()

instance Functor Identity where
    fmap f (Identity x) = Identity $ f x

instance Apply Identity where
    liftF2 f (Identity x) (Identity y) = Identity $ f x y



type instance CategoryOk U.Vector a = U.Unbox a

instance Functor U.Vector where
    fmap f xs = U.map f xs

instance Apply U.Vector where
    liftF2 f xs ys = U.zipWith f xs ys



type instance CategoryOk (Product f g) a = (CategoryOk f a, CategoryOk g a)

instance (Functor f, Functor g) => Functor (Product f g) where
    type ThisFunctorOk (Product f g) a = (FunctorOk f a, FunctorOk g a)
    fmap f (Pair xs ys) = Pair (fmap f xs) (fmap f ys)

instance (Apply f, Apply g) => Apply (Product f g) where
    type ThisApplyOk (Product f g) a = (ApplyOk f a, ApplyOk g a)
    liftF2 f (Pair xs xs') (Pair ys ys') =
        Pair (liftF2 f xs ys) (liftF2 f xs' ys')
