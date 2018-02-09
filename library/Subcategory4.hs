{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Subcategory4 where

import Prelude hiding (Functor(..))
import qualified Prelude as P

import qualified Control.Applicative as P
import Data.Constraint
-- import Data.Constraint.Forall
import Data.Either
import Data.Functor.Const
import Data.Functor.Identity
import Data.Kind
import Data.Proxy
import GHC.Generics

import Data.Vector as V
import Data.Vector.Unboxed as U



type ObjKind = Type
type MorKind = Type -> Type -> Type
type CatKind = Type
type FunKind = Type -> Type

class Category k where
    type Obj k (a :: ObjKind) :: Constraint
    -- type Obj k :: ObjKind -> Constraint
    -- type Mor k (m :: MorKind) :: Constraint

-- how to represent subcategories?

data Hask
class HaskC a
instance Category Hask where
    type Obj Hask a = ()
    -- type Obj Hask = HaskC
    -- type Mor Hask m = (m ~ (->))

data Numeric
class Numeric1 (f :: Type -> Type) where
    numF :: Num a :- Num (f a)
instance Category Numeric where
    type Obj Numeric a = Num a
    -- type Obj Numeric = Num
    -- type Mor Numeric m = (m ~ (->))

data Unboxed
class Unboxed1 (f :: Type -> Type) where
    unboxF :: U.Unbox a :- U.Unbox (f a)
instance Category Unboxed where
    type Obj Unboxed a = U.Unbox a
    -- type Obj Unboxed = U.Unbox
    -- type Mor Unboxed m = (m ~ (->))



-- | Morphisms are (generalized) functions, and can be mapped
-- (evaluated) to functions in Hask.
class Category (MorCat m) => Morphism (m :: MorKind) where
    type MorCat m :: CatKind
    chase :: (Obj (MorCat m) a, Obj (MorCat m) b) => m a b -> a -> b
    fromHask :: (Obj (MorCat m) a, Obj (MorCat m) b) => (a -> b) -> m a b
    -- fromHask . chase == id

-- MIdentity (MId)
-- MCompose (:@:) (>>>)

instance Morphism (->) where
    type MorCat (->) = Hask
    chase = id
    fromHask = id

newtype VVector a = VVector (V.Vector a)
    deriving (Eq, Ord, Read, Show)

newtype (.->) a b = NFun { getNFun :: a -> b }
instance Morphism (.->) where
    type MorCat (.->) = Numeric
    chase = getNFun
    fromHask = NFun

-- nummy :: ((a -> b) -> c -> d) -> (a .-> b) -> c .-> d
nummy :: ((a -> b) -> f a -> f b) -> (a .-> b) -> f a .-> f b
nummy f = NFun . f . getNFun

newtype (:->) a b = UFun { getUFun :: a -> b }
instance Morphism (:->) where
    type MorCat (:->) = Unboxed
    chase = getUFun
    fromHask = UFun

-- funny :: ((a -> b) -> c -> d) -> (a :-> b) -> c :-> d
funny :: ((a -> b) -> f a -> f b) -> (a :-> b) -> f a :-> f b
funny f = UFun . f . getUFun

newtype UVector a = UVector (U.Vector a)
    deriving (Eq, Ord, Read, Show)



class (Morphism m, Morphism (FunMor f m),
       Category (FunDom f m), Category (FunCod f m))
        => Functor (f :: FunKind) (m :: MorKind) where
    type FunMor f m :: MorKind
    cmap :: (Proxy f, Proxy m) -> Obj (FunDom f m) a :- Obj (FunCod f m) (f a)
    -- cmap _ = Sub Dict
    fmap :: (Obj (FunDom f m) a, Obj (FunDom f m) b)
            => m a b -> (FunMor f m) (f a) (f b)
type FunDom f m = (MorCat m :: CatKind)
type FunCod f m = (MorCat (FunMor f m) :: CatKind)

-- instance Obj (FunDom f m) a :=> Obj (FunCod f m) (f a) where ins = Sub Dict

-- funDomImpliesCod :: Functor f m
--                     => Obj (FunDom f m) a :- Obj (FunCod f m) (f a)
-- funDomImpliesCod _ = Sub (Obj (FunDom f m) a => Dict (Obj (FunCod f m) (f a)))
-- x = forall f m a . Functor f m => Dict (Obj (FunCod f m) (f a))
-- Dict (forall f m a . Functor f m => Obj (FunCod f m) (f a))

-- x = Dict :: Dict (Eq Int)
-- instance U.Unbox a :=> U.Unbox ((,) t a) where ins = Sub Dict



instance Functor Proxy (->) where
    type FunMor Proxy (->) = (->)
    cmap _ = Sub Dict
    fmap _ Proxy = Proxy

instance Functor Identity (->) where
    type FunMor Identity (->) = (->)
    cmap _ = Sub Dict
    fmap f (Identity x) = Identity (f x)

instance Functor (Either e) (->) where
    type FunMor (Either e) (->) = (->)
    cmap _ = Sub Dict
    fmap _ (Left a) = Left a
    fmap f (Right x) = Right (f x)

instance Functor ((,) t) (->) where
    type FunMor ((,) t) (->) = (->)
    cmap _ = Sub Dict
    fmap f (a, x) = (a, f x)

instance Functor ((->) a) (->) where
    type FunMor ((->) a) (->) = (->)
    fmap f fx = f . fx

instance (Functor f (->), Functor g (->),
          FunMor f (->) ~ (->), FunMor g (->) ~ (->))
        => Functor (f :+: g) (->) where
    type FunMor (f :+: g) (->) = (->)
    cmap _ = Sub Dict
    fmap f (L1 xs) = L1 (fmap f xs)
    fmap f (R1 ys) = R1 (fmap f ys)

instance (Functor f (->), Functor g (->),
          FunMor f (->) ~ (->), FunMor g (->) ~ (->))
        => Functor (f :*: g) (->) where
    type FunMor (f :*: g) (->) = (->)
    cmap _ = Sub Dict
    fmap f (xs :*: ys) = fmap f xs :*: fmap f ys

-- instance (Functor f (->), Functor g (->),
--           FunMor f (->) ~ (->), FunMor g (->) ~ (->))
--         => Functor (f :.: g) (->) where
--     type FunMor (f :.: g) (->) = (->)
--     cmap _ = Sub Dict
--     fmap f (Comp1 xss) = Comp1 (fmap (fmap f) xss)

instance Functor VVector (->) where
    type FunMor VVector (->) = (->)
    cmap _ = Sub Dict
    fmap f (VVector xs) = VVector (V.map f xs)



instance Num a => Num (Proxy a) where
    (+) = P.liftA2 (+)
    (*) = P.liftA2 (*)
    negate = P.fmap negate
    abs = P.fmap abs
    signum = P.fmap signum
    fromInteger = P.pure . fromInteger
-- instance Obj (FunDom Proxy (->)) a :=> Obj (FunCod Proxy (->)) (Proxy a) where ins = Sub Dict
-- instance Obj Numeric a :=> Obj Numeric (Proxy a) where ins = Sub Dict
-- instance Num a :=> Num (Proxy a) where ins = Sub Dict
instance Functor Proxy (.->) where
    type FunMor Proxy (.->) = (.->)
    cmap _ = Sub Dict
    fmap = nummy fmap'
        where fmap' _ Proxy = Proxy

instance Functor Identity (.->) where
    type FunMor Identity (.->) = (.->)
    cmap _ = Sub Dict
    fmap = nummy fmap'
        where fmap' f (Identity x) = Identity (f x)

instance Num a => Num (Either e a) where
    (+) = P.liftA2 (+)
    (*) = P.liftA2 (*)
    negate = P.fmap negate
    abs = P.fmap abs
    signum = P.fmap signum
    fromInteger = P.pure . fromInteger
-- instance Num a :=> Num (Either e a) where ins = Sub Dict
instance Functor (Either e) (.->) where
    type FunMor (Either e) (.->) = (.->)
    cmap _ = Sub Dict
    fmap = nummy fmap'
        where fmap' _ (Left a) = Left a
              fmap' f (Right x) = Right (f x)

instance (Monoid t, Num a) => Num (t, a) where
    (+) = P.liftA2 (+)
    (*) = P.liftA2 (*)
    negate = P.fmap negate
    abs = P.fmap abs
    signum = P.fmap signum
    fromInteger = P.pure . fromInteger
-- instance (Monoid t, Num a) :=> Num (t, a) where ins = Sub Dict
instance Monoid t => Functor ((,) t) (.->) where
    type FunMor ((,) t) (.->) = (.->)
    cmap _ = Sub Dict
    fmap = nummy fmap'
        where fmap' f (a, x) = (a, f x)

-- (.->)

-- (:+:)

instance (Num (f a), Num (g a)) => Num ((f :*: g) a) where
    (xs :*: ys) + (xs' :*: ys') = (xs + xs') :*: (ys + ys')
    (xs :*: ys) * (xs' :*: ys') = (xs * xs') :*: (ys * ys')
    negate (xs :*: ys) = negate xs :*: negate ys
    abs (xs :*: ys) = abs xs :*: abs ys
    signum (xs :*: ys) = signum xs :*: signum ys
    fromInteger a = fromInteger a :*: fromInteger a
-- instance (Num (f a), Num (g a)) :=> Num ((f :*: g) a) where ins = Sub Dict
-- instance (Functor f (.->), Functor g (.->),
--           FunMor f (.->) ~ (.->), FunMor g (.->) ~ (.->))
--         => Functor (f :*: g) (.->) where
--     type FunMor (f :*: g) (.->) = (.->)
--     cmap _ =
--         let
--             cmapf = cmap (Proxy :: Proxy f, Proxy :: Proxy (.->)) -- a :- f a
--             cmapg = cmap (Proxy :: Proxy g, Proxy :: Proxy (.->)) -- a :- g a
--         in cmapf &&& cmapg
--     fmap f = NFun (\(xs :*: ys) -> getNFun (fmap f) xs :*: getNFun (fmap f) ys)

instance Num (f (g a)) => Num ((f :.: g) a) where
    Comp1 xss + Comp1 yss = Comp1 (xss + yss)
    Comp1 xss * Comp1 yss = Comp1 (xss * yss)
    negate (Comp1 xss) = Comp1 (negate xss)
    abs (Comp1 xss) = Comp1 (abs xss)
    signum (Comp1 xss) = Comp1 (signum xss)
    fromInteger a = Comp1 (fromInteger a)
-- instance Num (f (g a)) :=> Num ((f :.: g) a) where ins = Sub Dict
-- instance (Functor f (.->), Functor g (.->),
--           FunMor f (.->) ~ (.->), FunMor g (.->) ~ (.->))
--         => Functor (f :.: g) (.->) where
--     type FunMor (f :.: g) (.->) = (.->)
--     fmap f = NFun (\(Comp1 xss) -> Comp1 (getNFun (fmap (fmap f)) xss))



-- Proxy is not unboxed. TODO: Implement this.
-- instance Functor Proxy (:->) where
--     type FunMor Proxy (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap = funny fmap'
--         where fmap' _ Proxy = Proxy

-- Identity is not unboxed. TODO: Implement this.
-- instance Functor Identity (:->) where
--     type FunMor Identity (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap = funny fmap'
--         where fmap' f (Identity x) = Identity (f x)

-- Either is not unboxed. TODO: Support #(|)#
-- instance Obj Unboxed a => Functor (Either e) (:->) where
--     type FunMor (Either e) (:->) = (->)
--     cmap _ = Sub Dict
--     fmap (UFun _) (Left a) = Left a
--     fmap (UFun f) (Right x) = Right (f x)

-- instance Obj Unboxed a => Functor ((,) t) (:->) where
--     type FunMor ((,) t) (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap = funny fmap'
--         where fmap' f (a, x) = (a, f x)

-- TODO: Fix this
-- instance Functor ((->) a) (:->) where
--     type FunMor ((->) a) (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap = funny fmap'
--         where fmap' f fx = f . fx

-- TODO: Think about this. Maybe state instead that (:->) is in Hask?
-- instance Functor ((:->) a) (:->) where
--     type FunMor ((:->) a) (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap = funny fmap'
--         where fmap' f (UFun fx) = UFun (f . fx)

-- instance (Functor f (:->), Functor g (:->),
--           FunMor f (:->) ~ (:->), FunMor g (:->) ~ (:->))
--         => Functor (f :+: g) (:->) where
--     type FunMor (f :+: g) (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap f = UFun (\case
--                     L1 xs -> L1 (getUFun (fmap f) xs)
--                     R1 ys -> R1 (getUFun (fmap f) ys))

-- TODO: Fix this
-- instance (Functor f (:->), Functor g (:->),
--           FunMor f (:->) ~ (:->), FunMor g (:->) ~ (:->))
--         => Functor (f :*: g) (:->) where
--     type FunMor (f :*: g) (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap f = UFun (\(xs :*: ys) -> getUFun (fmap f) xs :*: getUFun (fmap f) ys)

-- TODO:
-- instance (Functor f (:->), Functor g (:->),
--           FunMor f (:->) ~ (:->), FunMor g (:->) ~ (:->))
--         => Functor (f :.: g) (:->) where
--     type FunMor (f :.: g) (:->) = (:->)
--     cmap _ = Sub Dict
--     fmap f = UFun (\(Comp1 xss) -> Comp1 (getUFun (fmap (fmap f)) xss))

instance Functor UVector (:->) where
    type FunMor UVector (:->) = (->) -- not an endofunctor
    cmap _ = Sub Dict
    fmap (UFun f) (UVector xs) = UVector (U.map f xs)
