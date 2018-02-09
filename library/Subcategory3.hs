{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Subcategory3 where

import Data.Functor.Const
import Data.Functor.Identity
import Data.Kind
import Data.Proxy
import GHC.Generics

import Data.Vector as V
import Data.Vector.Unboxed as U

import Prelude hiding (Functor(..))
import qualified Prelude as P



--------------------------------------------------------------------------------



class Category k where
    type Obj k a :: Constraint

data Hask
instance Category Hask where type Obj Hask a = ()
data Numeric
instance Category Numeric where type Obj Numeric a = Num a
data Unboxed
instance Category Unboxed where type Obj Unboxed a = U.Unbox a



--------------------------------------------------------------------------------



-- | Morphisms are (generalized) functions, and can be mapped
-- ("evaluated") to functions in Hask.
type MKind = Type -> Type -> Type
class Category (MorCat m) => Morphism (m :: MKind) where
    type MorCat m
    eval :: m a b -> a -> b
-- data MIdentity a b = MIdentity
-- instance Morphism MIdentity where
--     eval MIdentity = id
data MCompose m m' b a c = MCompose (m b c) (m' a b)
instance (Morphism m, Morphism m', MorCat m ~ MorCat m')
        => Morphism (MCompose m m' b) where
    type MorCat (MCompose m m' b) = MorCat m
    eval (MCompose f g) = eval f . eval g
-- Functor, Monad, Profunctor

instance Morphism (->) where
    type MorCat (->) = Hask
    eval = id
newtype VVector a = VVector (V.Vector a)
    deriving (Eq, Ord, Read, Show)

newtype (:->) a b = UFun { getUFun :: a -> b }
instance Morphism (:->) where
    type MorCat (:->) = Unboxed
    eval = getUFun
-- funny :: ((a -> b) -> c -> d) -> (a :-> b) -> c :-> d
funny :: ((a -> b) -> f a -> f b) -> (a :-> b) -> f a :-> f b
funny f = UFun . f . getUFun
newtype UVector a = UVector (U.Vector a)
    deriving (Eq, Ord, Read, Show)



class Morphism m => Functor m f where
    fmap :: ( Obj (MorCat m) a
            , Obj (MorCat m) b
            -- , Obj (MorCat m) (f a)
            -- , Obj (MorCat m) (f b)
            )
            => m a b -> m (f a) (f b)

-- Functor? Endofunctor?

instance Functor (->) Proxy where
    fmap _ Proxy = Proxy
instance Functor (->) (Const a) where
    fmap _ (Const a) = Const a
instance Functor (->) Identity where
    fmap f (Identity x) = Identity (f x)
instance Functor (->) (Either a) where
    fmap _ (Left a) = Left a
    fmap f (Right x) = Right (f x)
instance Functor (->) ((,) a) where
    fmap f (a, x) = (a, f x)
instance Functor (->) ((->) a) where
    fmap f fx = f . fx
instance (Functor (->) f, Functor (->) g) => Functor (->) (f :+: g) where
    fmap f (L1 xs) = L1 (fmap f xs)
    fmap f (R1 ys) = R1 (fmap f ys)
instance (Functor (->) f, Functor (->) g) => Functor (->) (f :*: g) where
    fmap f (xs :*: ys) = fmap f xs :*: fmap f ys
instance (Functor (->) f, Functor (->) g) => Functor (->) (f :.: g) where
    fmap f (Comp1 xss) = Comp1 (fmap (fmap f) xss)
instance Functor (->) VVector where
    fmap f (VVector xs) = VVector (V.map f xs)

instance Functor (:->) Proxy where
    fmap = funny fmap'
        where fmap' _ Proxy = Proxy
instance Functor (:->) (Const a) where
    fmap = funny fmap'
        where fmap' _ (Const a) = Const a
instance Functor (:->) Identity where
    fmap = funny fmap'
        where fmap' f (Identity x) = Identity (f x)
instance Functor (:->) (Either a) where
    fmap = funny fmap'
        where fmap' _ (Left a) = Left a
              fmap' f (Right x) = Right (f x)
instance Functor (:->) ((,) a) where
    fmap = funny fmap'
        where fmap' f (a, x) = (a, f x)
instance Functor (:->) ((:->) a) where
    fmap = funny fmap'
        where fmap' f (UFun fx) = UFun (f . fx)
instance Unbox a => Functor (:->) ((->) a) where
    fmap = funny fmap'
        where fmap' f fx = f . fx
instance (Functor (:->) f, Functor (:->) g) => Functor (:->) (f :+: g) where
    fmap f = UFun (\case
                    L1 xs -> L1 (getUFun (fmap f) xs)
                    R1 ys -> R1 (getUFun (fmap f) ys))
instance (Functor (:->) f, Functor (:->) g) => Functor (:->) (f :*: g) where
    fmap f = UFun (\(xs :*: ys) -> getUFun (fmap f) xs :*: getUFun (fmap f) ys)
-- TODO
-- instance (Functor (:->) f, Functor (:->) g) => Functor (:->) (f :.: g) where
--     fmap f = UFun (\(Comp1 xss) -> Comp1 (getUFun (fmap (fmap f)) xss))
instance Functor (:->) UVector where
    fmap (UFun f) = UFun (\(UVector xs) -> UVector (U.map f xs))
