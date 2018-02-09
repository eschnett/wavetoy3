{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-unused-matches #-}

module Subcategory7 where

import Prelude hiding (Functor(..))
import qualified Prelude as P
import qualified Control.Monad as P

import Data.Constraint
import Data.Constraint.Forall
import Data.Functor.Identity
import Data.Kind
import GHC.Generics

import Data.Vector as V
import Data.Vector.Generic as G
import Data.Vector.Generic.Mutable as M
import Data.Vector.Unboxed as U



type ObjKind = Type
type MorKind = Type -> Type -> Type
type CatKind = Type
type FunKind = Type -> Type



--------------------------------------------------------------------------------



class Category (k :: CatKind) where
    type Obj k (a :: ObjKind) :: Constraint
    type Obj1 k :: ObjKind -> Constraint

class Category (Cat m) => Morphism (m :: MorKind) where
    type Cat m :: CatKind
    chase :: (Obj (Cat m) a, Obj (Cat m) b) => m a b -> a -> b
    fromHask :: (Obj (Cat m) a, Obj (Cat m) b) => (a -> b) -> m a b
data MIdentity k a b where
    MIdentity :: Obj k a => MIdentity k a a
instance Category k => Morphism (MIdentity k) where
    type Cat (MIdentity k) = k
    chase MIdentity = id
    fromHask f = undefined
data MCompose m n b a c = MCompose (m b c) (n a b)
instance (Morphism m, Morphism n, Cat m ~ Cat n, Obj (Cat m) b)
        => Morphism (MCompose m n b) where
    type Cat (MCompose m n b) = Cat m
    chase (MCompose f g) = chase f . chase g
    fromHask f = undefined



data Hask
class HaskC a
instance Category Hask where
    type Obj Hask a = ()
    type Obj1 Hask = HaskC
instance Morphism (->) where
    type Cat (->) = Hask
    chase = id
    fromHask = id



--------------------------------------------------------------------------------



data Numeric
instance Category Numeric where
    type Obj Numeric a = Num a
    type Obj1 Numeric = Num

newtype (.->) a b = NFun { runNFun :: a -> b }
instance Morphism (.->) where
    type Cat (.->) = Numeric
    chase = runNFun
    fromHask = NFun



testNumeric :: Floating a => [a -> a]
testNumeric =
    let m1 = NFun sin
        m2 = NFun cos
        m3 = MIdentity @ Numeric
        m4 = MCompose m1 m2
    in [chase m1, chase m2, chase m3, chase m4]



--------------------------------------------------------------------------------



data Unboxed
instance Category Unboxed where
    type Obj Unboxed a = U.Unbox a
    type Obj1 Unboxed = U.Unbox

newtype (:->) a b = UFun { runUFun :: a -> b }
instance Morphism (:->) where
    type Cat (:->) = Unboxed
    chase = runUFun
    fromHask = UFun



newtype Tuple a = Tuple (a, a)
    deriving (Eq, Ord, Read, Show)
newtype instance U.MVector s (Tuple a) = MV_Tuple (U.MVector s (a, a))
newtype instance U.Vector (Tuple a) = V_Tuple (U.Vector (a, a))
instance U.Unbox a => M.MVector U.MVector (Tuple a) where
    {-# INLINE basicLength #-}
    {-# INLINE basicUnsafeSlice #-}
    {-# INLINE basicOverlaps #-}
    {-# INLINE basicUnsafeNew #-}
    {-# INLINE basicInitialize #-}
    {-# INLINE basicUnsafeReplicate #-}
    {-# INLINE basicUnsafeRead #-}
    {-# INLINE basicUnsafeWrite #-}
    {-# INLINE basicClear #-}
    {-# INLINE basicSet #-}
    {-# INLINE basicUnsafeCopy #-}
    {-# INLINE basicUnsafeGrow #-}
    basicLength (MV_Tuple v) = M.basicLength v
    basicUnsafeSlice i n (MV_Tuple v) = MV_Tuple $ M.basicUnsafeSlice i n v
    basicOverlaps (MV_Tuple v1) (MV_Tuple v2) = M.basicOverlaps v1 v2
    basicUnsafeNew n = MV_Tuple `P.liftM` M.basicUnsafeNew n
    basicInitialize (MV_Tuple v) = M.basicInitialize v
    basicUnsafeReplicate n (Tuple x) =
        MV_Tuple `P.liftM` M.basicUnsafeReplicate n x
    basicUnsafeRead (MV_Tuple v) i = Tuple `P.liftM` M.basicUnsafeRead v i
    basicUnsafeWrite (MV_Tuple v) i (Tuple x) = M.basicUnsafeWrite v i x
    basicClear (MV_Tuple v) = M.basicClear v
    basicSet (MV_Tuple v) (Tuple x) = M.basicSet v x
    basicUnsafeCopy (MV_Tuple v1) (MV_Tuple v2) = M.basicUnsafeCopy v1 v2
    basicUnsafeMove (MV_Tuple v1) (MV_Tuple v2) = M.basicUnsafeMove v1 v2
    basicUnsafeGrow (MV_Tuple v) n = MV_Tuple `P.liftM` M.basicUnsafeGrow v n
instance U.Unbox a => G.Vector U.Vector (Tuple a) where
    {-# INLINE basicUnsafeFreeze #-}
    {-# INLINE basicUnsafeThaw #-}
    {-# INLINE basicLength #-}
    {-# INLINE basicUnsafeSlice #-}
    {-# INLINE basicUnsafeIndexM #-}
    {-# INLINE elemseq #-}
    basicUnsafeFreeze (MV_Tuple v) = V_Tuple `P.liftM` G.basicUnsafeFreeze v
    basicUnsafeThaw (V_Tuple v) = MV_Tuple `P.liftM` G.basicUnsafeThaw v
    basicLength (V_Tuple v) = G.basicLength v
    basicUnsafeSlice i n (V_Tuple v) = V_Tuple $ G.basicUnsafeSlice i n v
    basicUnsafeIndexM (V_Tuple v) i = Tuple `P.liftM` G.basicUnsafeIndexM v i
    basicUnsafeCopy (MV_Tuple mv) (V_Tuple v) = G.basicUnsafeCopy mv v
    elemseq _ (Tuple x) y = G.elemseq (undefined :: U.Vector (a, a)) x y
instance U.Unbox a => U.Unbox (Tuple a)

newtype UVector a = UVector (U.Vector a)
    deriving (Eq, Ord, Read, Show)
newtype VVector a = VVector (V.Vector a)
    deriving (Eq, Ord, Read, Show)

testTuple :: UVector (Tuple Int)
testTuple = UVector (U.singleton (Tuple (1, 2)))



class (Morphism m, Morphism n) => Functor f m n where
    -- fmap :: (Obj (Cat m) a, Obj (Cat m) b,
    --          Obj (Cat n) (f a), Obj (Cat n) (f b))
    --         => m a b -> n (f a) (f b)
    -- cmap :: Obj (Cat m) a :- Obj (Cat n) (f a)
    -- cmap :: Forall (Obj (Cat m)) => ForallF (Obj (Cat n)) f
    fmap :: (Obj (Cat m) a, Obj (Cat m) b) => m a b -> n (f a) (f b)



instance Functor Identity (->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Identity x) -> Identity (chase f x))
instance Functor Identity (.->) (.->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Identity x) -> Identity (chase f x))
instance Functor Identity (.->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Identity x) -> Identity (chase f x))
instance Functor Identity (:->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Identity x) -> Identity (chase f x))


instance Functor Tuple (:->) (:->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Tuple (x1, x2)) -> Tuple (chase f x1, chase f x2))
instance Functor Tuple (:->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Tuple (x1, x2)) -> Tuple (chase f x1, chase f x2))
instance Functor Tuple (.->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Tuple (x1, x2)) -> Tuple (chase f x1, chase f x2))
instance Functor Tuple (->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(Tuple (x1, x2)) -> Tuple (chase f x1, chase f x2))

instance Functor UVector (:->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(UVector x) -> UVector (U.map (chase f) x))

instance Functor VVector (:->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(VVector x) -> VVector (V.map (chase f) x))
instance Functor VVector (.->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(VVector x) -> VVector (V.map (chase f) x))
instance Functor VVector (->) (->) where
    -- cmap = Sub Dict
    fmap f = fromHask (\(VVector x) -> VVector (V.map (chase f) x))



--------------------------------------------------------------------------------



class a ~ Double => DoubleC a
instance Category Double where
    type Obj Double a = DoubleC a
    type Obj1 Double = DoubleC

data Affine a b = Affine b b
instance Morphism Affine where
    type Cat Affine = Double
    chase (Affine b m) x = m * x + b
    fromHask f = undefined

testAffine :: DoubleC a => [a -> a]
testAffine =
    let m1 = Affine 0 0
        m2 = Affine 1 0
        m3 = Affine 0 1
        m4 = Affine 1 1
        m5 = MIdentity @ Double
        m6 = MCompose m3 m5
        m7 = MCompose m2 m3
    in [chase m1, chase m2, chase m3, chase m4, chase m5, chase m6, chase m7]

-- instance Morphism UVector
-- instance Morphism VVector



--------------------------------------------------------------------------------



-- (:*:)

newtype instance U.MVector s ((f :*: g) a) = MV_Product (U.MVector s (f a, g a))
newtype instance U.Vector ((f :*: g) a) = V_Product (U.Vector (f a, g a))
instance (U.Unbox (f a), U.Unbox (g a))
        => M.MVector U.MVector ((f :*: g) a) where
    {-# INLINE basicLength #-}
    {-# INLINE basicUnsafeSlice #-}
    {-# INLINE basicOverlaps #-}
    {-# INLINE basicUnsafeNew #-}
    {-# INLINE basicInitialize #-}
    {-# INLINE basicUnsafeReplicate #-}
    {-# INLINE basicUnsafeRead #-}
    {-# INLINE basicUnsafeWrite #-}
    {-# INLINE basicClear #-}
    {-# INLINE basicSet #-}
    {-# INLINE basicUnsafeCopy #-}
    {-# INLINE basicUnsafeGrow #-}
    basicLength (MV_Product v) = M.basicLength v
    basicUnsafeSlice i n (MV_Product v) = MV_Product $ M.basicUnsafeSlice i n v
    basicOverlaps (MV_Product v1) (MV_Product v2) = M.basicOverlaps v1 v2
    basicUnsafeNew n = MV_Product `P.liftM` M.basicUnsafeNew n
    basicInitialize (MV_Product v) = M.basicInitialize v
    basicUnsafeReplicate n (x :*: y) =
        MV_Product `P.liftM` M.basicUnsafeReplicate n (x, y)
    basicUnsafeRead (MV_Product v) i =
        uncurry (:*:) `P.liftM` M.basicUnsafeRead v i
    basicUnsafeWrite (MV_Product v) i (x :*: y) =
        M.basicUnsafeWrite v i (x, y)
    basicClear (MV_Product v) = M.basicClear v
    basicSet (MV_Product v) (x :*: y) = M.basicSet v (x, y)
    basicUnsafeCopy (MV_Product v1) (MV_Product v2) = M.basicUnsafeCopy v1 v2
    basicUnsafeMove (MV_Product v1) (MV_Product v2) = M.basicUnsafeMove v1 v2
    basicUnsafeGrow (MV_Product v) n =
        MV_Product `P.liftM` M.basicUnsafeGrow v n
instance (U.Unbox (f a), U.Unbox (g a)) => G.Vector U.Vector ((f :*: g) a) where
    {-# INLINE basicUnsafeFreeze #-}
    {-# INLINE basicUnsafeThaw #-}
    {-# INLINE basicLength #-}
    {-# INLINE basicUnsafeSlice #-}
    {-# INLINE basicUnsafeIndexM #-}
    {-# INLINE elemseq #-}
    basicUnsafeFreeze (MV_Product v) = V_Product `P.liftM` G.basicUnsafeFreeze v
    basicUnsafeThaw (V_Product v) = MV_Product `P.liftM` G.basicUnsafeThaw v
    basicLength (V_Product v) = G.basicLength v
    basicUnsafeSlice i n (V_Product v) = V_Product $ G.basicUnsafeSlice i n v
    basicUnsafeIndexM (V_Product v) i =
        uncurry (:*:) `P.liftM` G.basicUnsafeIndexM v i
    basicUnsafeCopy (MV_Product mv) (V_Product v) = G.basicUnsafeCopy mv v
    elemseq _ (x :*: y) z =
        G.elemseq (undefined :: U.Vector (f a, g a)) (x, y) z
instance (U.Unbox (f a), U.Unbox (g a)) => U.Unbox ((f :*: g) a)

instance (Functor f (:->) (:->), Functor g (:->) (:->))
        => Functor (f :*: g) (:->) (:->) where
    -- -- cmap = Sub Dict
    -- -- cmap = cmap @ f &&& cmap @ g
    -- cmap = undefined
    fmap f = UFun (\(x :*: y) -> runUFun (fmap f) x :*: runUFun (fmap f) y)



instance (Functor f (:->) (->), Functor g (:->) (->))
        => Functor (f :+: g) (:->) (->) where
    -- cmap = Sub Dict
    fmap f (L1 x) = L1 (fmap f x)
    fmap f (R1 y) = R1 (fmap f y)

instance (Functor f (:->) (->), Functor g (:->) (->))
        => Functor (f :*: g) (:->) (->) where
    -- cmap = Sub Dict
    fmap f (x :*: y) = fmap f x :*: fmap f y

instance (Functor f (->) (->), Functor g (:->) (->))
        => Functor (f :.: g) (:->) (->) where
    -- cmap = Sub Dict
    fmap :: forall a b. (U.Unbox a, U.Unbox b)
            => (a :-> b) -> (f :.: g) a -> (f :.: g) b
    fmap f (Comp1 xy) = Comp1 (fmap (fmap f :: (g a -> g b)) xy)



instance (Functor f (->) (->), Functor g (->) (->))
        => Functor (f :+: g) (->) (->) where
    -- cmap = Sub Dict
    fmap f (L1 x) = L1 (fmap f x)
    fmap f (R1 y) = R1 (fmap f y)

instance (Functor f (->) (->), Functor g (->) (->))
        => Functor (f :*: g) (->) (->) where
    -- cmap = Sub Dict
    fmap f (x :*: y) = fmap f x :*: fmap f y

instance (Functor f (->) (->), Functor g (->) (->))
        => Functor (f :.: g) (->) (->) where
    -- cmap = Sub Dict
    fmap :: forall a b. (a -> b) -> (f :.: g) a -> (f :.: g) b
    fmap f (Comp1 xy) = Comp1 (fmap (fmap f :: (g a -> g b)) xy)



-- testUnboxed :: U.Unbox a => [a -> a]
-- testUnboxed =
--     let m1 = NFun sin
--         m2 = NFun cos
--         m3 = MIdentity @ Numeric
--         m4 = MCompose m1 m2
--     in [chase m1, chase m2, chase m3, chase m4]
