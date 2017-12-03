{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module ComonadicVector (ComonadicVector(..)) where

-- https://github.com/mikeizbicki/ifcxt

import Control.Applicative
import Control.Comonad
import Control.Comonad.Store
-- import Data.Distributive
import Data.Foldable
import Data.Maybe
import Data.Unfoldable
import Data.Validity
import Data.Validity.Vector ()
import qualified Data.Vector as V
import Data.VectorSpace
-- import Linear.Vector
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Function as QC



-- TODO: provide these instances for V.Vector, then use them here
data ComonadicVector v a = ComonadicVector
    { pos_ :: Int
    , elems_ :: v a
    } deriving (Eq, Ord, Read, Show, Foldable, Functor, Traversable)

instance (v ~ V.Vector, Validity (v a)) => Validity (ComonadicVector v a) where
    validate (ComonadicVector i xs) =
        mconcat
        [ i <?!> "Comonad position"
        , xs <?!> "vector"
        , i >= 0 && i < V.length xs <?@> "Comonad position is in range"
        ]
    isValid = isValidByValidating

instance v ~ V.Vector => Unfoldable (ComonadicVector v) where
    unfold xs = fmap mkvec ((:) <$> xs <*> unfold xs)
        where mkvec ys = ComonadicVector 0 (V.fromList ys)

-- This is probably the wrong (non-zippy) applicative
-- instance Applicative v => Applicative (ComonadicVector v) where
--     pure = undefined   -- don't know which length to choose
--     ComonadicVector pos1 funs <*> ComonadicVector pos2 args =
--         assert (pos1 == pos2) $
--         ComonadicVector 0 (funs <*> args)

instance v ~ V.Vector => Applicative (ComonadicVector v) where
    pure = undefined            -- don't know which length to choose
    ComonadicVector i funs <*> ComonadicVector j args =
        ComonadicVector (min i j) (V.zipWith id funs args)

-- TODO: Do we actually want this?
instance v ~ V.Vector => Alternative (ComonadicVector v) where
    empty = undefined           -- ComonadicVector cannot be empty
    ComonadicVector i xs <|> ComonadicVector j ys =
        ComonadicVector (i + j) (xs V.++ ys)

-- instance Monad
-- instance MonadPlus

-- instance v ~ V.Vector => Distributive (ComonadicVector v) where
--     -- collect :: Functor f => (a -> g b) -> f a -> g (f b)
--     collect f xs = ComonadicVector 0 $ V.generate n $ \i -> fmap (peek i . f) xs
--         where
--             n = 10

instance v ~ V.Vector => Comonad (ComonadicVector v) where
    extract (ComonadicVector i xs) = xs V.! i
    extend f arr@(ComonadicVector i xs) =
        ComonadicVector i (V.imap (\j _ -> f (arr {pos_ = j})) xs)

instance v ~ V.Vector => ComonadApply (ComonadicVector v)

instance v ~ V.Vector => ComonadStore Int (ComonadicVector v) where
    -- pos :: w a -> s
    pos (ComonadicVector i _) = i
    -- peek :: s -> w a -> a
    peek i (ComonadicVector _ xs) = xs V.! i

-- Indexed
-- Indexed Foldable
-- Indexed Functor
-- Indexed Applicative



instance (v ~ V.Vector, QC.Arbitrary a) =>
         QC.Arbitrary (ComonadicVector v a) where
    arbitrary = QC.scale (`div` 10) $ QC.sized $ \size -> do
        n <- QC.choose (1, size + 1)
        xs <- V.generateM n (const QC.arbitrary)
        i <- QC.choose (0, V.length xs - 1)
        return (ComonadicVector i xs)
    shrink (ComonadicVector i xs) =
        [ ComonadicVector (i `mod` length ys') (V.fromList ys')
        | ys' <- QC.shrink ys]
        where ys = toList xs

instance (v ~ V.Vector, QC.CoArbitrary a) =>
         QC.CoArbitrary (ComonadicVector v a) where
    coarbitrary = QC.coarbitrary . toList

instance (v ~ V.Vector, QC.Function a) =>
         QC.Function (ComonadicVector v a) where
    function = QC.functionMap toList (fromJust . fromList)



-- instance (Functor v, v ~ V.Vector) => Additive (ComonadicVector v) where
--     -- zero :: Num a => f a
--     zero = undefined
--     -- (^+^) :: Num a => f a -> f a -> f a
--     -- (^-^) :: Num a => f a -> f a -> f a

instance (Applicative (ComonadicVector v), AdditiveGroup a) =>
         AdditiveGroup (ComonadicVector v a) where
    zeroV = pure zeroV
    negateV = fmap negateV
    (^+^) = liftA2 (^+^)

instance (Applicative (ComonadicVector v), VectorSpace a) =>
         VectorSpace (ComonadicVector v a) where
    type Scalar (ComonadicVector v a) = Scalar a
    (*^) x = fmap (x *^)

instance (Foldable (ComonadicVector v), Applicative (ComonadicVector v),
          InnerSpace a) =>
    InnerSpace (ComonadicVector v a) where
        xs <.> ys = sumV $ (<.>) <$> xs <*> ys
