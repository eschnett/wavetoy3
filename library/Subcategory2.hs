{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Subcategory2 where



import Prelude hiding
    (Foldable(..), Functor(..), Applicative(..), Traversable(..))
import qualified Prelude as P

import Control.Applicative (ZipList(..))
import Data.Either
import Data.Functor.Const
import Data.Functor.Identity
import Data.Kind
import Data.Maybe
import Data.Monoid
import Data.Proxy
import GHC.Generics

import Data.Vector as V
import Data.Vector.Unboxed as U



-- | Morphisms are (generalized) functions, and can be mapped
-- ("evaluated") to functions in Hask.
type MKind = Type -> Type -> Type
class Morphism (m :: MKind) where
    eval :: m a b -> a -> b
-- data MIdentity a b = MIdentity
-- instance Morphism MIdentity where
--     eval MIdentity = id
data MCompose m m' b a c = MCompose (m b c) (m' a b)
instance (Morphism m, Morphism m') => Morphism (MCompose m m' b) where
    eval (MCompose f g) = eval f . eval g
-- Functor, Monad, Profunctor

instance Morphism (->) where
    eval = id



-- | We represent categories as constraints on the types, defining the
-- objects of the category.
class Category k where
    type Obj k a :: Constraint

data Hask
instance Category Hask where type Obj Hask a = ()
data Unboxed
instance Category Unboxed where type Obj Unboxed a = U.Unbox a
data Numeric
instance Category Numeric where type Obj Numeric a = Num a



class Category (Cat f) => Functor f where
    type Cat f
    -- fmap ::
    --     (Morphism m, Obj (Cat f) a, Obj (Cat f) b)
    --     => m a b -> f a -> f b
    -- default fmap ::
    --     (Endofunctor f, Morphism m,
    --      Obj (Cat f) a, Obj (Cat f) b, Obj (Cat f) (f a), Obj (Cat f) (f b))
    --     => m a b -> f a -> f b
    -- fmap = eval . emap
    fmap :: (Obj (Cat f) a, Obj (Cat f) b) => (a -> b) -> f a -> f b

class Functor f => Endofunctor f where
    emap ::
        (Obj (Cat f) a, Obj (Cat f) b, Obj (Cat f) (f a), Obj (Cat f) (f b))
        => (a -> b) -> f a -> f b
    emap = fmap

-- How do we express this property?
-- (Endofunctor f, Obj (Cat f) a) => Obj (Cat f) (f a)

-- class (Endofunctor f, ProveEndo f a) => ProveEndo f (f a)
--     proveEndo :: (Obj (Cat f) a, Obj (Cat f) (f a)) => a -> f a

-- (Endofunctor f, Obj (Cat f) a) => Obj (Cat f) (f a)

-- class ProveEndo f where
--     m :: forall a . (Endofunctor f, Obj (Cat f) a) => Obj (Cat f) (f a)

class Functor f => Foldable f where
    -- foldMap :: (Morphism m, Obj (Cat f) a, Monoid b) => m a b -> f a -> b
    foldMap :: (Obj (Cat f) a, Monoid b) => (a -> b) -> f a -> b

-- class Functor f => Apply f where
--     liftF2 ::
--         (Morphism m, Obj (Cat f) a, Obj (Cat f) b, Obj (Cat f) c)
--         => m a (m b c) -> f a -> f b -> f c
-- 
-- class Apply f => Applicative f where
--     pure :: Obj (Cat f) a => a -> f a
-- 
-- class Applicative m => Monad m where
--     return :: Obj (Cat m) a => a -> m a
--     return = pure
--     (>>=) :: (Obj (Cat m) a, Obj (Cat m) b) => m a -> (a -> m b) -> m b
-- 
-- class Functor t => Traversable t where
--     {-# MINIMAL traverse | sequenceA #-}
--     traverse ::
--         (Applicative f, Obj (Cat f) b, Obj (Cat t) a, Obj (Cat f) (t b))
--         => (a -> f b) -> t a -> f (t b)
--     default traverse ::
--         (Applicative f, Obj (Cat f) b, Obj (Cat t) a, Obj (Cat f) (t b),
--          Obj (Cat t) (f b), Obj (Cat t) b)
--         => (a -> f b) -> t a -> f (t b)
--     traverse f = sequenceA . fmap f
--     sequenceA ::
--         (Applicative f,
--          Obj (Cat f) a, Obj (Cat t) (f a), Obj (Cat t) a, Obj (Cat f) (t a))
--         => t (f a) -> f (t a)
--     sequenceA = traverse id
-- 
-- class Functor g => Distributive g where
--     {-# MINIMAL distribute | cotraverseMap #-}
--     collect ::
--         (Foldable f,
--          Obj (Cat g) b, Obj (Cat f) a, Obj (Cat f) b, Obj (Cat g) (f b))
--         => (a -> g b) -> f a -> g (f b)
--     collect f = cotraverseMap id f
--     distribute ::
--         (Foldable f,
--          Obj (Cat g) a, Obj (Cat f) (g a), Obj (Cat f) a, Obj (Cat g) (f a))
--         => f (g a) -> g (f a)
--     distribute = cotraverseMap id id
--     cotraverse ::
--         (Foldable f,
--          Obj (Cat f) a, Obj (Cat g) a, Obj (Cat f) (g a), Obj (Cat g) b)
--         => (f a -> b) -> f (g a) -> g b
--     cotraverse f = cotraverseMap f id
--     cotraverseMap ::
--         (Foldable f,
--          Obj (Cat f) b, Obj (Cat g) b, Obj (Cat f) a, Obj (Cat g) c)
--         => (f b -> c) -> (a -> g b) -> f a -> g c
--     default cotraverseMap ::
--         (Foldable f,
--          Obj (Cat f) b, Obj (Cat g) b, Obj (Cat f) a, Obj (Cat g) c,
--          Obj (Cat f) (g b), Obj (Cat g) (f b))
--         => (f b -> c) -> (a -> g b) -> f a -> g c
--     cotraverseMap f g = fmap f . distribute . fmap g
-- 
-- class Functor w => Comonad w where
--     {-# MINIMAL extract, (extend | duplicate) #-}
--     extract :: Obj (Cat w) a => w a -> a
--     extend :: (Obj (Cat w) a, Obj (Cat w) b) => (w a -> b) -> w a -> w b
--     default extend ::
--         (Endofunctor w, Obj (Cat w) a, Obj (Cat w) (w a), Obj (Cat w) b)
--         => (w a -> b) -> w a -> w b
--     extend f = fmap f . duplicate
--     duplicate ::
--         (Endofunctor w, Obj (Cat w) a, Obj (Cat w) (w a))
--         => w a -> w (w a)
--     duplicate = extend id
-- 
-- class Comonad w => ComonadStore s w | w -> s where
--     pos :: Obj (Cat w) a => w a -> s
--     peek :: Obj (Cat w) a => s -> w a -> a
--     peeks :: Obj (Cat w) a => (s -> s) -> w a -> a
--     seek :: Obj (Cat w) a => s -> w a -> w a
--     default seek ::
--         (Endofunctor w, Obj (Cat w) a, Obj (Cat w) (w a))
--         => s -> w a -> w a
--     seek s = peek s . duplicate
--     seeks :: Obj (Cat w) a => (s -> s) -> w a -> w a
--     default seeks ::
--         (Endofunctor w, Obj (Cat w) a, Obj (Cat w) (w a))
--         => (s -> s) -> w a -> w a
--     seeks f = peeks f . duplicate
--     experiment ::
--         (Functor f, Obj (Cat f) s, Obj (Cat w) a, Obj (Cat f) a)
--         => (s -> f s) -> w a -> f a
--     experiment f w = fmap (`peek` w) (f (pos w))



-- Proxy, Const a, Identity, Maybe, Either a, (a, ), (a ->), [],
-- ZipList, (:+:), (:*:), (:.:)

instance Functor Proxy where
    type Cat Proxy = Hask
    fmap f Proxy = Proxy
    -- fmap f = P.fmap (eval f)
instance Functor (Const a) where
    type Cat (Const a) = Hask
    fmap f (Const a) = Const a
    -- fmap f = P.fmap (eval f)
instance Functor Identity where
    type Cat Identity = Hask
    fmap f (Identity x) = Identity (f x)
    -- fmap f = P.fmap (eval f)
instance Functor Maybe where
    type Cat Maybe = Hask
    fmap f = maybe Nothing (Just . f)
    -- fmap f = P.fmap (eval f)
instance Functor (Either a) where
    type Cat (Either a) = Hask
    fmap f = either Left (Right . f)
    -- fmap f = P.fmap (eval f)
instance Functor ((,) a) where
    type Cat ((,) a) = Hask
    fmap f (a, x) = (a, f x)
    -- fmap f = P.fmap (eval f)
instance Functor ((->) a) where
    type Cat ((->) a) = Hask
    fmap f xs = f . xs
    -- fmap f = P.fmap (eval f)
instance Functor [] where
    type Cat [] = Hask
    fmap f = P.map f
    -- fmap f = P.fmap (eval f)
instance Functor ZipList where
    type Cat ZipList = Hask
    fmap f = P.fmap f
    -- fmap f = P.fmap (eval f)
instance (Functor f, Functor g, Cat f ~ Cat g) => Functor (f :+: g) where
    type Cat (f :+: g) = Cat f
    -- fmap f (L1 xs) = L1 (fmap (eval f) xs)
    -- fmap f (R1 xs) = R1 (fmap (eval f) xs)
    fmap f (L1 xs) = L1 (fmap f xs)
    fmap f (R1 xs) = R1 (fmap f xs)
instance (Functor f, Functor g, Cat f ~ Cat g) => Functor (f :*: g) where
    type Cat (f :*: g) = Cat f
    -- fmap f (xs :*: ys) = fmap (eval f) xs :*: fmap (eval f) ys
    fmap f (xs :*: ys) = fmap f xs :*: fmap f ys
--TODO instance (Functor f, Endofunctor g, Cat f ~ Cat g) => Functor (f :.: g) where
--TODO     type Cat (f :.: g) = Cat f
--TODO     -- fmap f (Comp1 xss) = Comp1 (fmap (eval emap (eval f)) xss)
--TODO     -- Could not deduce: (Obj (Cat g) (g a), Obj (Cat g) (g b))
--TODO     fmap f (Comp1 xss) = Comp1 (fmap (emap f) xss)

instance Endofunctor Proxy
instance Endofunctor (Const a)
instance Endofunctor Identity
instance Endofunctor Maybe
instance Endofunctor (Either a)
instance Endofunctor ((,) a)
instance Endofunctor ((->) a)
instance Endofunctor []
instance Endofunctor ZipList
