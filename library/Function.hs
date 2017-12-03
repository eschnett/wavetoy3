{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Function
  ( Function(..)
  , Discretization(..)
  , Integrable(..)
  , Differentiable(..)
  , FIdentity(..)
  , FVoid(..)
  , FUnit(..)
  , FConst(..)
  , FCompose(..)
  , FProd(..)
  , FSum(..)
  , FCurry(..)
  , FUncurry(..)
  ) where

import Data.Kind
import Data.Tuple.Extra ((&&&), swap)
import Data.VectorSpace
import Data.Void
import GHC.Generics
-- import Numeric.AD hiding (Scalar(..))
-- import Numeric.AD.Mode.Forward
-- import Numeric.AD.Mode.Reverse
import qualified Test.QuickCheck as QC

import Integration



--------------------------------------------------------------------------------

-- | A typeclass for functions
class Function f where
  -- | A constraint defining which domains and codomains are valid
  type FunctionOk f a b :: Constraint
  -- | Evaluate a function. This is always possible, and is a
  -- natural transformation from 'f' to 'Hask'. This also makes 'f'
  -- a concrete category.
  eval :: FunctionOk f a b => f a b -> a -> b

class Function f => Discretization f where
  -- | Discretize a function from Hask to this representation. This
  -- is a natural transformation from 'Hask' to 'f'. Generically,
  -- this is a lossy operation.
  --
  -- prop> discretized . eval == id
  -- prop> eval . discretized == id   -- as much as possible
  discretized :: FunctionOk f a b => (a -> b) -> f a b

class Function f => Integrable f where
  type IntegrableOk f a b :: Constraint
  integral :: (FunctionOk f a b, IntegrableOk f a b) => f a b -> b

class Function f => Differentiable f where
  type DifferentiableOk f a b :: Constraint
  type Dir f :: Type
  boundary ::
       (FunctionOk f a b, DifferentiableOk f a b) => Dir f -> f a b -> f a b
  derivative ::
       (FunctionOk f a b, DifferentiableOk f a b) => Dir f -> f a b -> f a b



--------------------------------------------------------------------------------

-- | The identity function
data FIdentity a b where
  FIdentity :: FIdentity a b
  deriving (Generic, Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance QC.Arbitrary (FIdentity a b) where
  arbitrary = return FIdentity

instance Function FIdentity where
  type FunctionOk FIdentity a b = a ~ b
  eval FIdentity = id

instance Integrable FIdentity where
  type IntegrableOk FIdentity a b = (Bounded a, Real a)
  integral FIdentity = (maxBound - minBound) `asInTypeOf` FIdentity

asInTypeOf :: a -> f a b -> a
asInTypeOf x _ = x
-- asOutTypeOf :: b -> f a b -> b
-- asOutTypeOf x _ = x



-- | The void function, which does not accept any argument
data FVoid a b where
  FVoid :: FVoid a b
  deriving (Generic, Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance QC.Arbitrary (FVoid a b) where
  arbitrary = return FVoid

instance Function FVoid where
  type FunctionOk FVoid a b = a ~ Void
  eval FVoid = absurd

instance Integrable FVoid where
  type IntegrableOk FVoid a b = AdditiveGroup b
  integral FVoid = zeroV

instance Discretization FVoid where
  discretized _ = FVoid



-- | The unit function, which forgets its argument
data FUnit a b where
  FUnit :: FUnit a b
  deriving (Generic, Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance QC.Arbitrary (FUnit a b) where
  arbitrary = return FUnit

instance Function FUnit where
  type FunctionOk FUnit a b = b ~ ()
  eval FUnit = const ()



-- | Another possible unit function
data FConst a b where
  FConst :: b -> FConst a b
  deriving (Generic, Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance QC.Arbitrary b => QC.Arbitrary (FConst a b) where
  arbitrary = [FConst x | x <- QC.arbitrary]
  shrink = QC.genericShrink

instance Function FConst where
  type FunctionOk FConst a b = ()
  eval (FConst x) = const x

-- instance Function FConst => Discretization FConst where
--     discretized _ = undefined       -- TODO

instance Integrable FConst where
  type IntegrableOk FConst a b = ( Bounded a
                                 , Real a
                                 , VectorSpace b
                                 , Fractional (Scalar b))
  integral f@(FConst x) = realToFrac ((maxBound - minBound) `asInTypeOf` f) *^ x

instance Differentiable FConst where
  type DifferentiableOk FConst a b = AdditiveGroup b
  type Dir FConst = ()
  boundary () (FConst _) = FConst zeroV
  derivative () (FConst _) = FConst zeroV



-- | Compose two functions
data FCompose f g c a b where
  FCompose :: f c b -> g a c -> FCompose f g c a b
  deriving (Generic, Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance (QC.Arbitrary (f c b), QC.Arbitrary (g a c)) =>
         QC.Arbitrary (FCompose f g c a b) where
  arbitrary = [FCompose f g | f <- QC.arbitrary, g <- QC.arbitrary]
  shrink = QC.genericShrink

instance (Function f, Function g) => Function (FCompose f g c) where
  type FunctionOk (FCompose f g c) a b = (FunctionOk f c b, FunctionOk g a c)
  eval (FCompose f g) = eval f . eval g

instance (Differentiable f, Differentiable g) =>
         Differentiable (FCompose f g c) where
  type DifferentiableOk (FCompose f g c) a b = ( DifferentiableOk f c b
                                               , DifferentiableOk g a c)
  type Dir (FCompose f g c) = Either (Dir f) (Dir g)
  boundary (Left dir) (FCompose f g) = FCompose (boundary dir f) g
  boundary (Right dir) (FCompose f g) = FCompose f (boundary dir g)
  derivative (Left dir) (FCompose f g) = FCompose (derivative dir f) g
  derivative (Right dir) (FCompose f g) = FCompose f (derivative dir g)



-- | Product of two functions
data FProd f g b c a d where
  FProd :: f a b -> g a c -> FProd f g b c a (b, c)

deriving instance
         (Eq (f a b), Eq (g a c)) => Eq (FProd f g b c a (b, c))

deriving instance
         (Ord (f a b), Ord (g a c)) => Ord (FProd f g b c a (b, c))

deriving instance
         (Read (f a b), Read (g a c)) => Read (FProd f g b c a (b, c))

deriving instance
         (Show (f a b), Show (g a c)) => Show (FProd f g b c a (b, c))

deriving instance
         (Foldable (f a), Foldable (g a)) => Foldable (FProd f g b c a)

instance (QC.Arbitrary (f a b), QC.Arbitrary (g a c)) =>
         QC.Arbitrary (FProd f g b c a (b, c)) where
  arbitrary = [FProd f g | f <- QC.arbitrary, g <- QC.arbitrary]
  shrink (FProd f g) = [FProd f' g' | (f', g') <- QC.shrink (f, g)]

instance (Function f, Function g) => Function (FProd f g b c) where
  type FunctionOk (FProd f g b c) a d = ( FunctionOk f a b
                                        , FunctionOk g a c
                                        , d ~ (b, c))
  eval (FProd f g) = eval f &&& eval g

instance (Function (FProd f g b c), Discretization f, Discretization g) =>
         Discretization (FProd f g b c) where
  discretized f = FProd (discretized (fst . f)) (discretized (snd . f))

instance (Integrable f, Integrable g) => Integrable (FProd f g b c) where
  type IntegrableOk (FProd f g b c) a d = ( IntegrableOk f a b
                                          , IntegrableOk g a c)
  -- TODO: this use be (*) instead of (,); do we need to introduce
  -- IntegralType for this?
  integral (FProd f g) = (integral f, integral g)

instance (Differentiable f, Differentiable g) =>
         Differentiable (FProd f g b c) where
  type DifferentiableOk (FProd f g b c) a d = ( DifferentiableOk f a b
                                              , DifferentiableOk g a c)
  type Dir (FProd f g b c) = (Dir f, Dir g)
  boundary (dirf, dirg) (FProd f g) = FProd (boundary dirf f) (boundary dirg g)
  derivative (dirf, dirg) (FProd f g) =
    FProd (derivative dirf f) (derivative dirg g)



-- | Sum of two functions
data FSum f g a b d c where
  FSum :: f a c -> g b c -> FSum f g a b (Either a b) c

deriving instance
         (Eq (f a c), Eq (g b c)) => Eq (FSum f g a b (Either a b) c)

deriving instance
         (Ord (f a c), Ord (g b c)) => Ord (FSum f g a b (Either a b) c)

deriving instance
         (Read (f a c), Read (g b c)) => Read (FSum f g a b (Either a b) c)

deriving instance
         (Show (f a c), Show (g b c)) => Show (FSum f g a b (Either a b) c)

deriving instance
         (Foldable (f a), Foldable (g b)) =>
         Foldable (FSum f g a b (Either a b))

deriving instance
         (Functor (f a), Functor (g b)) =>
         Functor (FSum f g a b (Either a b))

deriving instance
         (Traversable (f a), Traversable (g b)) =>
         Traversable (FSum f g a b (Either a b))

instance (QC.Arbitrary (f a c), QC.Arbitrary (g b c)) =>
         QC.Arbitrary (FSum f g a b (Either a b) c) where
  arbitrary = [FSum f g | f <- QC.arbitrary, g <- QC.arbitrary]
  shrink (FSum f g) = [FSum f' g' | (f', g') <- QC.shrink (f, g)]

instance (Function f, Function g) => Function (FSum f g a b) where
  type FunctionOk (FSum f g a b) d c = ( FunctionOk f a c
                                       , FunctionOk g b c
                                       , d ~ Either a b)
  eval (FSum f g) = either (eval f) (eval g)

instance (Function (FSum f g a b), Discretization f, Discretization g) =>
         Discretization (FSum f g a b) where
  discretized f = FSum (discretized (f . Left)) (discretized (f . Right))

instance (Integrable f, Integrable g) => Integrable (FSum f g a b) where
  type IntegrableOk (FSum f g a b) d c = ( IntegrableOk f a c
                                         , IntegrableOk g b c
                                         , d ~ Either a b
                                         , AdditiveGroup c)
    -- TODO: How should the result be combined?
  integral (FSum f g) = integral f ^+^ integral g

instance (Differentiable f, Differentiable g) =>
         Differentiable (FSum f g a b) where
  type DifferentiableOk (FSum f g a b) d c = ( DifferentiableOk f a c
                                             , DifferentiableOk g b c
                                             , d ~ Either a b)
  type Dir (FSum f g a b) = (Dir f, Dir g)
  boundary (dirf, dirg) (FSum f g) = FSum (boundary dirf f) (boundary dirg g)
  derivative (dirf, dirg) (FSum f g) =
    FSum (derivative dirf f) (derivative dirg g)

-- | Monoidal, Braided, Symmetric:
-- fswap :: FProd f g b c a (b, c) -> FProd g f c b a (c, b)
-- fswap (FProd f g) = FProd g f
-- | Cartesian:
-- ffst :: FProd f g b c a (b, c) -> f a b
-- ffst (FProd f g) = f
-- fsnd :: FProd f g b c a (b, c) -> g a c
-- fsnd (FProd f g) = g
-- fdup :: f a b -> FProd f f b b a (b, b)
-- fdup f = FProd f f
-- fconst :: (Function f, FunctionOk f a b) => b -> f a b
-- fconst x = discretized (const x)



-- | Currying a function (in a closed category)
data FCurry f b c a d where
  FCurry :: f (a, b) c -> FCurry f b c a (FCurry' f a b c)

-- | Helper type for currying.
-- This is equivalent to a lambda capturing the function and its first argument.
data FCurry' f a b c where
  FCurry' :: f (a, b) c -> a -> FCurry' f a b c
  deriving (Generic)

deriving instance
         Eq (f (a, b) c) => Eq (FCurry f b c a (FCurry' f a b c))

deriving instance
         Ord (f (a, b) c) => Ord (FCurry f b c a (FCurry' f a b c))

deriving instance
         Read (f (a, b) c) => Read (FCurry f b c a (FCurry' f a b c))

deriving instance
         Show (f (a, b) c) => Show (FCurry f b c a (FCurry' f a b c))

deriving instance (Eq (f (a, b) c), Eq a) => Eq (FCurry' f a b c)

deriving instance
         (Ord (f (a, b) c), Ord a) => Ord (FCurry' f a b c)

deriving instance
         (Read (f (a, b) c), Read a) => Read (FCurry' f a b c)

deriving instance
         (Show (f (a, b) c), Show a) => Show (FCurry' f a b c)

instance QC.Arbitrary (f (a, b) c) =>
         QC.Arbitrary (FCurry f b c a (FCurry' f a b c)) where
  arbitrary = [FCurry f | f <- QC.arbitrary]
  shrink (FCurry f) = [FCurry f' | f' <- QC.shrink f]

instance (QC.Arbitrary (f (a, b) c), QC.Arbitrary a) =>
         QC.Arbitrary (FCurry' f a b c) where
  arbitrary = [FCurry' f x | f <- QC.arbitrary, x <- QC.arbitrary]
  shrink (FCurry' f x) = [FCurry' f' x' | (f', x') <- QC.shrink (f, x)]

instance Function f => Function (FCurry f b c) where
  type FunctionOk (FCurry f b c) a d = FunctionOk (FCurry' f a) b c
  eval (FCurry f) = FCurry' f

instance Function f => Function (FCurry' f a) where
  type FunctionOk (FCurry' f a) b c = FunctionOk f (a, b) c
  eval (FCurry' f x) y = eval f (x, y)



-- | Uncurrying a function (in a closed category)
data FUncurry f g a b d c where
  FUncurry :: f a (g b c) -> FUncurry f g a b (a, b) c

deriving instance
         Eq (f a (g b c)) => Eq (FUncurry f g a b (a, b) c)

deriving instance
         Ord (f a (g b c)) => Ord (FUncurry f g a b (a, b) c)

deriving instance
         Read (f a (g b c)) => Read (FUncurry f g a b (a, b) c)

deriving instance
         Show (f a (g b c)) => Show (FUncurry f g a b (a, b) c)

instance QC.Arbitrary (f a (g b c)) =>
         QC.Arbitrary (FUncurry f g a b (a, b) c) where
  arbitrary = [FUncurry f | f <- QC.arbitrary]
  shrink (FUncurry f) = [FUncurry f' | f' <- QC.shrink f]

instance (Function f, Function g) => Function (FUncurry f g a b) where
  type FunctionOk (FUncurry f g a b) d c = ( FunctionOk f a (g b c)
                                           , FunctionOk g b c
                                           , d ~ (a, b))
  eval (FUncurry f) (x, y) = eval (eval f x) y

instance (Function (FUncurry f g a b), Discretization f, Discretization g) =>
         Discretization (FUncurry f g a b) where
  discretized f = FUncurry $ discretized $ \x -> discretized $ \y -> f (x, y)



-- | Flipping argument order of a function (in a closed category)
-- data FFlip f g a b c
-- data FApply f a b = FApply f a b
-- data FApply f a (FApply g b c)
fflip
  :: ( Function f
     , Function g
     , FunctionOk f a (g b c)
     , FunctionOk g b c
     , FunctionOk g b (f a c)
     , FunctionOk f a c
     )
  => f a (g b c)
  -> FCurry
       (FFlip' (FUncurry f g a b) a b)
       a
       c
       b
       (FCurry' (FFlip' (FUncurry f g a b) a b) b a c)
fflip = FCurry . FFlip' . FUncurry

data FFlip' f a b d c where
  FFlip' :: f (a, b) c -> FFlip' f a b (b, a) c

instance Function f => Function (FFlip' f a b) where
  type FunctionOk (FFlip' f a b) d c = (FunctionOk f (a, b) c, d ~ (b, a))
  eval (FFlip' f) = eval f . swap



--------------------------------------------------------------------------------

-- | A 'Hask' function is trivially a 'Function'
instance Function (->) where
  type FunctionOk (->) a b = ()
  eval = id

-- | A 'Hask' function is a trivial discretization
instance Discretization (->) where
  discretized = id

-- | A 'Hask' function can be integrated
instance Integrable (->) where
  type IntegrableOk (->) a b = ( Bounded a
                               , RealFrac a
                               , InnerSpace b
                               , Floating (Scalar b)
                               , Ord (Scalar b))
  integral f = integrate f minBound maxBound

-- -- | A 'Hask' function has a derivative
-- instance Differentiable (->) where
--     type DifferentiableOk (->) a b = (Num a, a ~ b)
--     type Dir (->) = ()
--     boundary () f = 0
--     derivative () f = diff f
