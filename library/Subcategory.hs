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

module Subcategory where

import Control.Applicative (ZipList(..))
import qualified Control.Applicative as P
import Control.Exception (assert)
import Data.Either
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Kind
import Data.Maybe
import Data.Monoid hiding (Product, Sum, (<>))
import qualified Data.Vector.Unboxed as U
import Data.Proxy
import Data.Semigroup hiding (Product, Sum)
import Data.Validity
import GHC.TypeLits
import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , (<$>)
                      , Applicative(..)
                      , Traversable(..)
                      )
import qualified Prelude as P
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Function as QC



--------------------------------------------------------------------------------



-- | Is type 'a' in category 'k'?
type family CategoryOk (k :: Type -> Type) a :: Constraint



-- TODO: Introduce EndoFunctor that guarantees CateogoryOk a =>
-- CateogoryOk (f a)

-- TODO: Instead of the above, define categories via constraints, and
-- make that constraint a parameter to functor declarations

-- TODO: Instead of using a constraint, maybe use an abstract
-- identifier, and have a function CategoryOk?

type FunctorOk f a = (CategoryOk f a, ThisFunctorOk f a)

class Functor f where
    {-# MINIMAL fmap #-}

    type ThisFunctorOk f a :: Constraint
    type ThisFunctorOk f a = ()

    fmap :: (FunctorOk f a, FunctorOk f b) => (a -> b) -> f a -> f b

infixl 4 <$>
(<$>) :: (Functor f, FunctorOk f a, FunctorOk f b) => (a -> b) -> f a -> f b
(<$>) = fmap
{-# INLINE (<$>) #-}

prop_Functor_id :: ( Functor f
                   , FunctorOk f a
                   , Eq (f a), Show (f a)
                   )
                  => f a -> QC.Property
prop_Functor_id xs = fmap id xs QC.=== xs

prop_Functor_comp :: ( Functor f
                     , FunctorOk f a, FunctorOk f b, FunctorOk f c
                     , Eq (f a), Show (f a)
                     , Eq (f b), Show (f b)
                     , Eq (f c), Show (f c)
                     )
                    => (a -> b) -> (b -> c) -> f a -> QC.Property
prop_Functor_comp f g xs = (fmap g . fmap f) xs QC.=== fmap (g . f) xs

prop_Functor_Id :: (Eq a, Eq b, Show a, Show b) => (a -> b) -> a -> QC.Property
prop_Functor_Id f x = (fmap f . Identity) x QC.=== (Identity . f) x

prop_Functor_Comp :: ( Functor f
                     , Functor g
                     , FunctorOk g a
                     , FunctorOk f (g a)
                     , FunctorOk g b
                     , FunctorOk f (g b)
                     , FunctorOk (Compose f g) a
                     , FunctorOk (Compose f g) b
                     , Eq (f (g a))
                     , Eq (Compose f g b)
                     , Show (f (g a))
                     , Show (Compose f g b)
                     ) =>
                     (a -> b) -> f (g a) -> QC.Property
prop_Functor_Comp f xss =
    (fmap f . Compose) xss QC.=== (Compose . (fmap . fmap) f) xss



-- TODO: Given foldMap, is every Foldable a Functor?

type FoldableOk f a = (CategoryOk f a, FunctorOk f a, ThisFoldableOk f a)

class Functor t => Foldable t where
    {-# MINIMAL foldr | foldMap #-}

    type ThisFoldableOk t a :: Constraint
    type ThisFoldableOk t a = ()

    fold :: (FoldableOk t m, Monoid m) => t m -> m
    fold = foldMap id
    {-# INLINE fold #-}

    foldr :: FoldableOk t a => (a -> b -> b) -> b -> t a -> b
    foldr f z = (flip appEndo) z . foldMap (Endo . f)
    {-# INLINE foldr #-}

    foldl :: FoldableOk t a => (b -> a -> b) -> b -> t a -> b
    foldl f z = (flip appEndo) z . getDual . foldMap (Dual . Endo . flip f)
    {-# INLINE foldl #-}

    foldMap :: (FoldableOk t a, Monoid m) => (a -> m) -> t a -> m
    -- foldMap f = foldl (\r x -> r `mappend` f x) mempty
    foldMap f = foldr f' mempty
        where f' x r = f x `mappend` r
    {-# INLINE foldMap #-}



type ApplyOk f a = (CategoryOk f a, FunctorOk f a, ThisApplyOk f a)

class Functor f => Apply f where
    {-# MINIMAL (<.>) | liftF2 #-}

    type ThisApplyOk f a :: Constraint
    type ThisApplyOk f a = ()

    infixl 4 <.>
    (<.>) :: (ApplyOk f (a -> b), ApplyOk f a, ApplyOk f b)
             => f (a -> b) -> f a -> f b
    (<.>) = liftF2 id
    {-# INLINE (<.>) #-}

    liftF2 :: (ApplyOk f a, ApplyOk f b, ApplyOk f c)
              => (a -> b -> c) -> f a -> f b -> f c
    default liftF2 :: ( ApplyOk f a
                      , ApplyOk f b
                      , ApplyOk f c
                      , ApplyOk f (b -> c)
                      )
                     => (a -> b -> c) -> f a -> f b -> f c
    liftF2 f xs ys = f <$> xs <.> ys
    {-# INLINE liftF2 #-}

prop_Apply_assoc :: ( Apply f
                    , ApplyOk f a
                    , ApplyOk f b
                    , ApplyOk f c
                    , ApplyOk f ((a, b), c)
                    , ApplyOk f (a, b)
                    , ApplyOk f (b, c)
                    , ApplyOk f (a, (b, c))
                    , Eq (f a)
                    , Eq (f b)
                    , Eq (f c)
                    , Eq (f ((a, b), c))
                    , Show (f a)
                    , Show (f b)
                    , Show (f c)
                    , Show (f ((a, b), c))
                    )
                   => f a -> f b -> f c -> QC.Property
-- (.) <$> u <.> v <.> w = u <.> (v <.> w)
prop_Apply_assoc xs ys zs =
    liftF2 (,) (liftF2 (,) xs ys) zs QC.===
    (assoc <$> liftF2 (,) xs (liftF2 (,) ys zs))
    where assoc (x, (y, z)) = ((x, y), z)

prop_Apply_fmap_inner :: ( Apply f
                         , ApplyOk f a
                         , ApplyOk f b
                         , ApplyOk f (a, c)
                         , ApplyOk f (a, b)
                         , ApplyOk f c
                         , Eq (f a)
                         , Eq (f b)
                         , Eq (f (a, c))
                         , Show (f a)
                         , Show (f b)
                         , Show (f (a, c))
                         )
                        => (b -> c) -> f a -> f b -> QC.Property
-- x <.> (f <$> y) = (. f) <$> x <.> y
prop_Apply_fmap_inner f xs ys =
    liftF2 (,) xs (f <$> ys) QC.=== liftF2 ((. f) . (,)) xs ys

prop_Apply_fmap_outer :: ( Apply f
                         , ApplyOk f a
                         , ApplyOk f b
                         , ApplyOk f c
                         , ApplyOk f (a, b)
                         , Eq (f a)
                         , Eq (f b)
                         , Eq (f c)
                         , Show (f a)
                         , Show (f b)
                         , Show (f c)
                         )
                        => ((a, b) -> c) -> f a -> f b -> QC.Property
-- f <$> (x <.> y) = (f .) <$> x <.> y
prop_Apply_fmap_outer f xs ys =
    (f <$> liftF2 (,) xs ys) QC.=== liftF2 ((f .) . (,)) xs ys



type ApplicativeOk f a = (CategoryOk f a, ApplyOk f a, ThisApplicativeOk f a)

class Apply f => Applicative f where
    {-# MINIMAL pure #-}

    type ThisApplicativeOk f a :: Constraint
    type ThisApplicativeOk f a = ()

    pure :: ApplicativeOk f a => a -> f a

    (<*>) :: (ApplicativeOk f (a -> b), ApplicativeOk f a, ApplicativeOk f b)
             => f (a -> b) -> f a -> f b
    (<*>) = (<.>)
    {-# INLINE (<*>) #-}

    liftA2 :: (ApplicativeOk f a, ApplicativeOk f b, ApplicativeOk f c)
              => (a -> b -> c) -> f a -> f b -> f c
    liftA2 = liftF2
    {-# INLINE liftA2 #-}

-- prop_Applicative_id :: ( Applicative f
--                        , ApplicativeOk f a
--                        , ApplicativeOk f (a -> a)
--                        , Eq (f a)
--                        , Show (f a)
--                        )
--                       => f a -> QC.Property
-- prop_Applicative_id xs = pure id <*> xs QC.=== xs

prop_Applicative_id :: ( Applicative f
                       , ApplicativeOk f b
                       , ApplicativeOk f (a, b)
                       , ApplicativeOk f a
                       , Eq a
                       , Eq (f b)
                       , Eq (f (a, b))
                       , Show a
                       , Show (f b)
                       , Show (f (a, b))
                       )
                      => a -> f b -> QC.Property
prop_Applicative_id x ys = liftF2 (,) (pure x) ys QC.=== ((x,) <$> ys)

-- prop_Applicative_comp :: ( Applicative f
--                          , ApplicativeOk f (b -> c)
--                          , ApplicativeOk f (a -> b)
--                          , ApplicativeOk f a
--                          , ApplicativeOk f c
--                          , ApplicativeOk f ((b -> c) -> (a -> b) -> a -> c)
--                          , ApplicativeOk f (a -> c)
--                          , ApplicativeOk f ((a -> b) -> a -> c)
--                          , ApplicativeOk f b
--                          , Eq (f a)
--                          , Eq (f c)
--                          , Show (f a)
--                          , Show (f c)
--                          )
--                         => f (b -> c) -> f (a -> b) -> f a -> QC.Property
-- prop_Applicative_comp xs ys zs =
--     pure (.) <*> xs <*> ys <*> zs QC.=== xs <*> (ys <*> zs)
-- 
-- prop_Applicative_homo :: forall f a b .
--                          ( Applicative f
--                          , ApplicativeOk f (a -> b)
--                          , ApplicativeOk f a
--                          , ApplicativeOk f b
--                          , Eq (f a)
--                          , Eq (f b)
--                          , Show (f a)
--                          , Show (f b)
--                          )
--                          => Proxy f -> (a -> b) -> a -> QC.Property
-- prop_Applicative_homo proxy f x =
--     pure f <*> pure x QC.=== (pure (f x) :: f b)
-- 
-- prop_Applicative_interchange :: ( Applicative f
--                                 , ApplicativeOk f (a -> b)
--                                 , ApplicativeOk f b
--                                 , ApplicativeOk f a
--                                 , ApplicativeOk f ((a -> b) -> b)
--                                 , Eq b
--                                 , Eq (f b)
--                                 , Show b
--                                 , Show (f b)
--                                 )
--                                 => f (a -> b) -> a -> QC.Property
-- prop_Applicative_interchange xs y =
--     xs <*> pure y QC.=== pure ($ y) <*> xs



type TraversableOk f a =
    (CategoryOk f a, FoldableOk f a, FunctorOk f a, ThisTraversableOk f a)

class (Foldable t, Functor t) => Traversable t where
    type ThisTraversableOk t a :: Constraint
    type ThisTraversableOk t a = ()

    {-# MINIMAL traverse | sequenceA #-}

    -- | Map each element of a structure to an action, evaluate these
    -- actions from left to right, and collect the results.
    traverse :: ( Applicative f
                , ApplicativeOk f b
                , TraversableOk t a
                , TraversableOk t b
                , ApplicativeOk f (t b)
                )
               => (a -> f b) -> t a -> f (t b)
    default traverse :: ( Applicative f
                        , ApplicativeOk f b
                        , TraversableOk t a
                        , TraversableOk t b
                        , ApplicativeOk f (t b)
                        , TraversableOk t (f b)
                        )
                       => (a -> f b) -> t a -> f (t b)
    traverse f = sequenceA . fmap f
    {-# INLINE traverse #-}

    -- | Evaluate each action in the structure from left to right, and
    -- and collect the results.
    sequenceA :: ( Applicative f
                 , ApplicativeOk f a
                 , TraversableOk t (f a)
                 , TraversableOk t a
                 , ApplicativeOk f (t a)
                 )
                => t (f a) -> f (t a)
    sequenceA = traverse id
    {-# INLINE sequenceA #-}

    -- -- | Is this useful?
    -- traverse' :: ( Applicative f
    --              , TraversableOk t a
    --              , ApplicativeOk f a
    --              , TraversableOk t (f a)
    --              , ApplicativeOk f b
    --              )
    --             => (t a -> b) -> t (f a) -> f b
    -- default traverse' :: ( Applicative f
    --                      , TraversableOk t a
    --                      , ApplicativeOk f a
    --                      , TraversableOk t (f a)
    --                      , ApplicativeOk f b
    --                      , ApplicativeOk f (t a)
    --                      )
    --                     => (t a -> b) -> t (f a) -> f b
    -- traverse' f = fmap f . sequenceA
    -- {-# INLINE traverse' #-}

    -- traverseMap :: (a -> f b) -> (t b -> c) -> t a -> f c
    -- traverseMap f g = traverse g . fmap f



prop_Traversable_id :: ( Traversable t
                       , TraversableOk t a
                       , Eq (t a), Show (t a)
                       )
                      => t a -> QC.Property
prop_Traversable_id xs = traverse Identity xs QC.=== Identity xs

prop_Traversable_comp :: ( Applicative f
                         , Applicative g
                         , Traversable t
                         , ApplicativeOk f b
                         , ApplicativeOk g c
                         , TraversableOk t a
                         , TraversableOk t c
                         , ApplicativeOk (Compose f g) (t c)
                         , ApplicativeOk f (g c)
                         , TraversableOk t b
                         , ApplicativeOk f (t b)
                         , Eq ((Compose f g) (t c))
                         , Show ((Compose f g) (t c))
                         )
                        =>
                        (a -> f b) -> (b -> g c) -> t a -> QC.Property
prop_Traversable_comp f g xs =
    traverse (Compose . fmap g . f) xs QC.===
    (Compose . fmap (traverse g) . traverse f) xs



type DistributiveOk g a =
    (CategoryOk g a, FunctorOk g a, ThisDistributiveOk g a)
type DistributiveOk' g f a b c =
    ( Foldable f
    , Functor f
    , FoldableOk f b
    , FunctorOk f b
    , DistributiveOk g b
    , FoldableOk f a
    , FunctorOk f a
    , DistributiveOk g c
    , ThisDistributiveOk' g f a b c
    )

class Functor g => Distributive g where
    {-# MINIMAL distribute | cotraverseMap #-}

    type ThisDistributiveOk g a :: Constraint
    type ThisDistributiveOk g a = ()

    type ThisDistributiveOk' g (f :: Type -> Type) a b c :: Constraint
    type ThisDistributiveOk' g f a b c = ()

    collect :: ( Foldable f
               , Functor f
               , DistributiveOk g b
               , FoldableOk f a
               , FunctorOk f a
               , FoldableOk f b
               , FunctorOk f b
               , DistributiveOk g (f b)
               , DistributiveOk' g f a b (f b)
               )
              => (a -> g b) -> f a -> g (f b)
    collect f = cotraverseMap id f
    {-# INLINE collect #-}

    distribute :: ( Foldable f
                  , Functor f
                  , DistributiveOk g a
                  , FoldableOk f (g a)
                  , FunctorOk f (g a)
                  , FoldableOk f a
                  , FunctorOk f a
                  , DistributiveOk g (f a)
                  , DistributiveOk' g f (g a) a (f a)
                  )
                 => f (g a) -> g (f a)
    distribute = cotraverseMap id id
    {-# INLINE distribute #-}

    cotraverse :: ( Foldable f
                  , Functor f
                  , FoldableOk f a
                  , FunctorOk f a
                  , DistributiveOk g a
                  , FoldableOk f (g a)
                  , FunctorOk f (g a)
                  , DistributiveOk g b
                  , DistributiveOk' g f (g a) a b
                  )
                 => (f a -> b) -> f (g a) -> g b
    cotraverse f = cotraverseMap f id
    {-# INLINE cotraverse #-}

    -- | collect and cotraverse combined
    cotraverseMap :: ( Foldable f
                     , Functor f
                     , FoldableOk f b
                     , FunctorOk f b
                     , DistributiveOk g b
                     , FoldableOk f a
                     , FunctorOk f a
                     , DistributiveOk g c
                     , DistributiveOk' g f a b c
                     )
                    => (f b -> c) -> (a -> g b) -> f a -> g c
    default cotraverseMap :: ( Foldable f
                             , Functor f
                             , FoldableOk f b
                             , FunctorOk f b
                             , DistributiveOk g b
                             , FoldableOk f a
                             , FunctorOk f a
                             , DistributiveOk g c
                             , FoldableOk f (g b)
                             , FunctorOk f (g b)
                             , DistributiveOk g (f b)
                             , DistributiveOk' g f a b c
                             , DistributiveOk' g f (g b) b (f b)
                             )
                            => (f b -> c) -> (a -> g b) -> f a -> g c
    cotraverseMap f g = fmap f . distribute . fmap g
    {-# INLINE cotraverseMap #-}



type ComonadOk f a = (CategoryOk f a, FunctorOk f a, ThisComonadOk f a)

class Functor w => Comonad w where
    {-# MINIMAL extract, (duplicate | extend) #-}

    type ThisComonadOk w a :: Constraint
    type ThisComonadOk w a = ()

    extract :: ComonadOk w a => w a -> a

    duplicate :: (ComonadOk w a, ComonadOk w (w a)) => w a -> w (w a)
    duplicate = extend id
    {-# INLINE duplicate #-}

    extend :: (ComonadOk w a, ComonadOk w b) => (w a -> b) -> w a -> w b
    default extend :: ( ComonadOk w a
                      , ComonadOk w b
                      , ComonadOk w (w a)
                      )
                     => (w a -> b) -> w a -> w b
    extend f = fmap f . duplicate
    {-# INLINE extend #-}



type ComonadApplyOk w a =
    (CategoryOk w a, ComonadOk w a, ApplyOk w a, ThisComonadApplyOk w a)

class (Comonad w, Apply w) => ComonadApply w where
    type ThisComonadApplyOk w a :: Constraint
    type ThisComonadApplyOk w a = ()

-- | Lift a binary function into a comonad with zipping
liftW2 :: ( ComonadApply w
          , ComonadApplyOk w a
          , ComonadApplyOk w b
          , ComonadApplyOk w c
          )
         => (a -> b -> c) -> w a -> w b -> w c
liftW2 = liftF2
{-# INLINE liftW2 #-}



type ComonadStoreOk w a =
    (CategoryOk w a, ComonadOk w a, ThisComonadStoreOk w a)

class Comonad w => ComonadStore s w | w -> s where
    type ThisComonadStoreOk w a :: Constraint
    type ThisComonadStoreOk w a = (CategoryOk w a, ComonadOk w a)

    pos :: ComonadStoreOk w a => w a -> s
    peek :: ComonadStoreOk w a => s -> w a -> a

    peeks :: ComonadStoreOk w a => (s -> s) -> w a -> a
    peeks f w = peek (f (pos w)) w

    seek :: ComonadStoreOk w a => s -> w a -> w a
    default seek :: (ComonadStoreOk w a, ComonadStoreOk w (w a))
                    => s -> w a -> w a
    seek s = peek s . duplicate

    seeks :: ComonadStoreOk w a => (s -> s) -> w a -> w a
    default seeks :: (ComonadStoreOk w a, ComonadStoreOk w (w a))
                     => (s -> s) -> w a -> w a
    seeks f = peeks f . duplicate

    experiment :: ( Functor f
                  , FunctorOk f s
                  , ComonadStoreOk w a
                  , FunctorOk f a
                  )
                 => (s -> f s) -> w a -> f a
    experiment f w = fmap (`peek` w) (f (pos w))



--------------------------------------------------------------------------------



type instance CategoryOk Proxy a = ()
type instance CategoryOk (Const a) b = ()
type instance CategoryOk Identity a = ()
type instance CategoryOk Maybe a = ()
type instance CategoryOk (Either a) b = ()
type instance CategoryOk ((,) a) b = ()
type instance CategoryOk ((->) a) b = ()
type instance CategoryOk [] a = ()
type instance CategoryOk ZipList a = ()

type instance CategoryOk (Product f g) a = (CategoryOk f a, CategoryOk g a)
type instance CategoryOk (Sum f g) a = (CategoryOk f a, CategoryOk g a)
type instance CategoryOk (Compose f g) a = (CategoryOk g a, CategoryOk f (g a))



instance Foldable Proxy where
    foldMap = P.foldMap
instance Foldable (Const a) where
    foldMap = P.foldMap
instance Foldable Identity where
    foldMap = P.foldMap
instance Foldable Maybe where
    foldMap = P.foldMap
instance Foldable (Either a) where
    foldMap = P.foldMap
instance Foldable ((,) a) where
    foldMap = P.foldMap
instance Foldable [] where
    foldMap = P.foldMap
instance Foldable ZipList where
    foldMap = P.foldMap
instance (Foldable f, Foldable g) => Foldable (Product f g) where
    type ThisFoldableOk (Product f g) a = (FoldableOk f a, FoldableOk g a)
    foldMap f (Pair xs ys) = foldMap f xs `mappend` foldMap f ys
instance (Foldable f, Foldable g) => Foldable (Sum f g) where
    type ThisFoldableOk (Sum f g) a = (FoldableOk f a, FoldableOk g a)
    foldMap f (InL xs) = foldMap f xs
    foldMap f (InR ys) = foldMap f ys
instance (Foldable f, Foldable g) => Foldable (Compose f g) where
    type ThisFoldableOk (Compose f g) a = (FoldableOk g a, FoldableOk f (g a))
    foldMap f (Compose xss) = foldMap (foldMap f) xss

instance Functor Proxy where
    fmap = P.fmap
instance Functor (Const a) where
    fmap = P.fmap
instance Functor Identity where
    fmap = P.fmap
instance Functor Maybe where
    fmap = P.fmap
instance Functor (Either a) where
    fmap = P.fmap
instance Functor ((,) a) where
    fmap = P.fmap
instance Functor ((->) a) where
    fmap = P.fmap
instance Functor [] where
    fmap = P.fmap
instance Functor ZipList where
    fmap = P.fmap
instance (Functor f, Functor g) => Functor (Product f g) where
    type ThisFunctorOk (Product f g) a = (FunctorOk f a, FunctorOk g a)
    fmap f (Pair xs ys) = Pair (fmap f xs) (fmap f ys)
instance (Functor f, Functor g) => Functor (Sum f g) where
    type ThisFunctorOk (Sum f g) a = (FunctorOk f a, FunctorOk g a)
    fmap f (InL xs) = InL $ fmap f xs
    fmap f (InR ys) = InR $ fmap f ys
instance (Functor f, Functor g) => Functor (Compose f g) where
    type ThisFunctorOk (Compose f g) a = (FunctorOk g a, FunctorOk f (g a))
    fmap f (Compose xss) = Compose $ fmap (fmap f) xss

instance Apply Proxy where
    liftF2 = P.liftA2
instance Semigroup a => Apply (Const a) where
    liftF2 f (Const sx) (Const sy) = Const (sx <> sy)
instance Apply Identity where
    liftF2 = P.liftA2
instance Apply Maybe where
    liftF2 = P.liftA2
instance Apply (Either a) where
    liftF2 = P.liftA2
instance Semigroup a => Apply ((,) a) where
    liftF2 f (sx, x) (sy, y) = (sx <> sy, f x y)
instance Apply ((->) a) where
    liftF2 = P.liftA2
instance Apply [] where
    liftF2 = P.liftA2
instance Apply ZipList where
    liftF2 = P.liftA2
instance (Apply f, Apply g) => Apply (Product f g) where
    type ThisApplyOk (Product f g) a = (ApplyOk f a, ApplyOk g a)
    liftF2 f (Pair xs xs') (Pair ys ys') =
        Pair (liftF2 f xs ys) (liftF2 f xs' ys')
instance (Apply f, Apply g) => Apply (Compose f g) where
    type ThisApplyOk (Compose f g) a = (ApplyOk g a, ApplyOk f (g a))
    liftF2 f (Compose xss) (Compose yss) =
        Compose $ liftF2 (liftF2 f) xss yss

instance Applicative Proxy where
    pure = P.pure
instance (Semigroup a, Monoid a) => Applicative (Const a) where
    pure = P.pure
instance Applicative Identity where
    pure = P.pure
instance Applicative Maybe where
    pure = P.pure
instance Applicative (Either a) where
    pure = P.pure
instance (Semigroup a, Monoid a) => Applicative ((,) a) where
    pure = P.pure
instance Applicative ((->) a) where
    pure = P.pure
instance Applicative [] where
    pure = P.pure
instance Applicative ZipList where
    pure = P.pure
instance (Applicative f, Applicative g) => Applicative (Product f g) where
    type ThisApplicativeOk (Product f g) a =
        (ApplicativeOk f a, ApplicativeOk g a)
    pure x = Pair (pure x) (pure x)
instance (Applicative f, Applicative g) => Applicative (Compose f g) where
    type ThisApplicativeOk (Compose f g) a =
        (ApplicativeOk g a, ApplicativeOk f (g a))
    pure x = Compose $ pure (pure x)

instance Traversable Proxy where
    traverse f Proxy = pure Proxy
    -- traverse' f Proxy = pure (f Proxy)
instance Monoid a => Traversable (Const a) where
    traverse f (Const a) = pure (Const a)
    -- traverse' f (Const a) = pure (f (Const a))
instance Traversable Identity where
    traverse f (Identity x) = Identity <$> f x
    -- traverse' f (Identity xs) = f . Identity <$> xs
instance Traversable Maybe where
    traverse f Nothing = pure Nothing
    traverse f (Just x) = Just <$> f x
    -- traverse' f Nothing = pure (f Nothing)
    -- traverse' f (Just xs) = f . Just <$> xs
instance Traversable (Either a) where
    traverse f (Left a) = pure (Left a)
    traverse f (Right x) = Right <$> f x
    -- traverse' f (Left a) = pure (f (Left a))
    -- traverse' f (Right xs) = f . Right <$> xs
instance Traversable ((,) a) where
    traverse f (a, x) = (a, ) <$> f x
    -- traverse' f (a, xs) = f . (a, ) <$> xs
instance Traversable [] where
    traverse f = foldr f' (pure [])
        where f' x ys = liftA2 (:) (f x) ys
    -- traverse' f = error "impossible"
instance Traversable ZipList where
    traverse f = foldr f' (pure znil)
        where f' x ys = liftA2 zcons (f x) ys
              znil = ZipList []
              zcons x (ZipList xs) = ZipList (x:xs)
    -- traverse' f = error "impossible"
--TODO --TODO instance (Traversable f, Traversable g) => Traversable (Product f g) where
--TODO --TODO     type TraversableOk (Product f g) a =
--TODO --TODO         ( FoldableOk (Product f g) a
--TODO --TODO         , FunctorOk (Product f g) a
--TODO --TODO         , TraversableOk f a, TraversableOk g a
--TODO --TODO         )
--TODO --TODO     traverse f (Pair xs ys) = liftA2 Pair (traverse f xs) (traverse f ys)
--TODO --TODO     sequenceA = _
--TODO -- instance (Traversable f, Traversable g) => Traversable (Sum f g) where
--TODO --     type TraversableOk (Sum f g) a =
--TODO --         ( CategoryOk (Sum f g) a
--TODO --         , FoldableOk (Sum f g) a, FunctorOk (Sum f g) a
--TODO --         , TraversableOk f a, TraversableOk g a
--TODO --         )
--TODO --     traverse f (InL xs) = InL <$> traverse f xs
--TODO --     traverse f (InR ys) = InR <$> traverse f ys
--TODO -- instance (Traversable f, Traversable g) => Traversable (Compose f g) where
--TODO --     type TraversableOk (Compose f g) a =
--TODO --         ( CategoryOk (Compose f g) a
--TODO --         , TraversableOk g a, TraversableOk f (g a)
--TODO --         )
--TODO --     traverse f (Compose xss) = Compose <$> traverse (traverse f) xss

instance Distributive Proxy where
    cotraverseMap f g = const Proxy
instance Monoid a => Distributive (Const a) where
    cotraverseMap f g = fmap f . Const . foldMap (getConst . g)
instance Distributive Identity where
    cotraverseMap f g = Identity . f . fmap (runIdentity . g)
instance Distributive Maybe where
    cotraverseMap f g xs = if getAll (foldMap (All . isJust . g) xs)
                           then Just (f (fmap (fromJust . g) xs))
                           else Nothing
-- Semigroup would suffice here
instance Monoid a => Distributive (Either a) where
    cotraverseMap f g xs =
        if getAll (foldMap (All . isRight . g) xs)
        then Right (f (fmap ((\(Right x) -> x) . g) xs))
        else Left (foldMap (\x -> either id (const mempty) (g x)) xs)
instance Monoid a => Distributive ((,) a) where
    cotraverseMap f g xs = (foldMap (fst . g) xs, f (fmap (snd . g) xs))
instance Distributive ((->) a) where
    cotraverseMap f g xs = \a -> f (fmap (flip g a) xs)
instance (Distributive f, Distributive g) => Distributive (Product f g) where
    type ThisDistributiveOk (Product f g) a =
        (DistributiveOk f a, DistributiveOk g a)
    type ThisDistributiveOk' (Product f g) f1 a b c =
        (DistributiveOk' f f1 a b c, DistributiveOk' g f1 a b c)
    cotraverseMap f g xs =
        Pair (cotraverseMap f (fstP . g) xs) (cotraverseMap f (sndP . g) xs)
        where fstP (Pair l _) = l
              sndP (Pair _ r) = r
instance (Distributive f, Distributive g) => Distributive (Compose f g) where
    type ThisDistributiveOk (Compose f g) a =
        (DistributiveOk g a, DistributiveOk f (g a))
    type ThisDistributiveOk' (Compose f g) f1 a b c =
        ( DistributiveOk' f f1 a (g b) (g c), DistributiveOk' g f1 (g b) b c)
    cotraverseMap f g = Compose . cotraverseMap (cotraverse f) (getCompose . g)

-- Comonad
-- ComonadApply
-- ComonadStore (?)



newtype WrapHask f a = WrapHask { getWrapHask :: f a }
    deriving (Eq, Ord, Read, Show, QC.Arbitrary)

type instance CategoryOk (WrapHask f) a = ()

instance (P.Foldable t, P.Functor t) => Foldable (WrapHask t) where
    foldl f z = P.foldl f z . getWrapHask
    foldMap f = P.foldMap f . getWrapHask

instance P.Functor f => Functor (WrapHask f) where
    fmap f = WrapHask . P.fmap f . getWrapHask

instance P.Applicative f => Apply (WrapHask f) where
    WrapHask fs <.> WrapHask xs = WrapHask (fs P.<*> xs)
    liftF2 f (WrapHask xs) (WrapHask ys) = WrapHask (P.liftA2 f xs ys)

instance P.Applicative f => Applicative (WrapHask f) where
    pure = WrapHask . P.pure
    WrapHask fs <*> WrapHask xs = WrapHask (fs P.<*> xs)
    liftA2 f (WrapHask xs) (WrapHask ys) = WrapHask (P.liftA2 f xs ys)



--------------------------------------------------------------------------------



data Store s a = Store (s -> a) s

store :: (s -> a) -> s -> Store s a
store = Store

runStore :: Store s a -> (s -> a, s)
runStore (Store f s) = (f, s)

instance (QC.Arbitrary (QC.Fun s a), QC.Arbitrary s)
        => QC.Arbitrary (Store s a) where
    arbitrary = do wf <- QC.arbitrary
                   s <- QC.arbitrary
                   return (Store (QC.applyFun wf) s)

type instance CategoryOk (Store s) a = ()

instance Functor (Store s) where
    fmap f (Store wf s) = Store (f . wf) s

instance Semigroup s => Apply (Store s) where
    Store ff m <.> Store fx n = Store (ff <.> fx) (m <> n)

instance (Semigroup s, Monoid s) => Applicative (Store s) where
    pure x = Store (const x) mempty

instance Comonad (Store s) where
    extract (Store wf s) = wf s
    extend f (Store wf s) = Store (f . Store wf) s

instance Apply (Store s) => ComonadApply (Store s)

instance ComonadStore s (Store s) where
    pos (Store _ s) = s
    peek s (Store wf _) = wf s
    seek s (Store wf _) = Store wf s
    


--------------------------------------------------------------------------------



type instance CategoryOk U.Vector a = U.Unbox a

instance (U.Unbox a, Validity a) => Validity (U.Vector a) where
    validate xs = foldMap validate xs
    isValid = isValidByValidating

instance Foldable U.Vector where
    foldMap f = U.foldl' f' mempty
        where f' r x = r `mappend` f x

instance Functor U.Vector where
    fmap = U.map

instance Apply U.Vector where
    liftF2 = U.zipWith

-- instance Traversable U.Vector where
--     traverse f = U.foldl' (\r x -> liftA2 U.snoc r (f x)) (pure U.empty)
--     -- traverse f xs = fmap (U.fromListN n) $ P.traverse f $ U.toList $ xs
--     --     where n = U.length xs



-- newtype NVector (n :: Nat) a = NVector { getNVector :: U.Vector a }
--     deriving (Eq, Ord, Read, Show, Foldable, Functor, Apply)
-- 
-- type instance CategoryOk (NVector n) a = CategoryOk U.Vector a
-- 
-- instance (Apply (NVector n), KnownNat n) => Applicative (NVector n) where
--     pure x = NVector (U.replicate n x)
--         where n = fromInteger (natVal (Proxy :: Proxy n))
-- 
-- instance Traversable (NVector n) where
--     -- traverse f (NVector xs) = fmap NVector (U.foldl' (\y x -> y <*> x)
--     sequenceA (NVector xs) = 



data CVector (n :: Nat) a =
    CVector { getIndex :: !Int, getVector :: U.Vector a }
    deriving (Eq, Ord, Read, Show)

instance (KnownNat n, U.Unbox a, Validity (U.Vector a))
        => Validity (CVector n a) where
    validate (CVector i xs) =
        (i <?!> "Index") `mappend`
        (xs <?!> "Vector") `mappend`
        (U.length xs == n <?@> "Vector has correct length") `mappend`
        (i >= 0 && i < n <?@> "Index i is in bounds")
        where n = fromInteger (natVal (Proxy :: Proxy n))
    isValid = isValidByValidating

instance (KnownNat n, U.Unbox a, QC.Arbitrary a)
        => QC.Arbitrary (CVector n a) where
    arbitrary = do
        i <- QC.choose (0, n - 1)
        xs <- U.generateM n (const QC.arbitrary)
        return (CVector i xs)
        where n = fromInteger (natVal (Proxy :: Proxy n))
    shrink (CVector i xs) =
        [CVector i' xs | i' <- QC.shrink i] ++
        [CVector i (U.fromList ys') | ys' <- shrink' (U.toList xs)]
        where shrink' [] = []
              shrink' (y:ys) = [y':ys | y' <- QC.shrink y] ++
                               [y:ys' | ys' <- shrink' ys]

type instance CategoryOk (CVector n) a = CategoryOk U.Vector a

instance Foldable (CVector n) where
    foldMap f (CVector _ xs) = foldMap f xs

instance Functor (CVector n) where
    fmap f (CVector i xs) = CVector i (fmap f xs)

instance Apply (CVector n) where
    liftF2 f (CVector _ xs) (CVector _ ys) = CVector 0 (liftF2 f xs ys)

instance (KnownNat n, 1 <= n) => Applicative (CVector n) where
    pure x = CVector 0 (U.replicate n x)
        where n = fromInteger (natVal (Proxy :: Proxy n))

-- instance Traversable (CVector n) where
--     -- traverse f (CVector i xs) = CVector i <$> traverse f xs
--     traverse f (CVector i xs) =
--         U.foldl' (\r x -> liftA2 snoc' r (f x)) (pure empty') xs
--         where snoc' (CVector j ys) y = CVector j (U.snoc ys y)
--               empty' = CVector i U.empty

instance KnownNat n => Distributive (CVector n) where
    cotraverseMap f g xs = CVector 0 (U.generate n gen)
        where gen i = f (fmap (elt i . g) xs)
              elt i (CVector _ ys) = ys U.! i
              n = fromInteger (natVal (Proxy :: Proxy n))

instance (KnownNat n, 1 <= n) => Comonad (CVector n) where
    extract (CVector i xs) = xs U.! i
    extend f (CVector i xs) = CVector i (U.generate n gen)
        where gen j = f (CVector j xs)
              n = fromInteger (natVal (Proxy :: Proxy n))

instance (KnownNat n, 1 <= n) => ComonadStore Int (CVector n) where
    pos (CVector i _) = i
    peek i (CVector _ xs) = assert (i >= 0 && i < n) $ xs U.! i
        where n = fromInteger (natVal (Proxy :: Proxy n))
    seek i (CVector _ xs) = assert (i >= 0 && i < n) $ CVector i xs
        where n = fromInteger (natVal (Proxy :: Proxy n))
    seeks f (CVector i xs) = CVector (f i) xs
