{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ComonadicVectorSpec where

import Control.Comonad
import Control.Comonad.Store
import Data.Foldable
import Data.Unfoldable
import Data.Validity
import qualified Data.Vector as V
import Data.VectorSpace
import Test.QuickCheck
import Test.QuickCheck.Function

import ComonadicVector



prop_ComonadicVector_valid :: ComonadicVector V.Vector Double -> Bool
prop_ComonadicVector_valid = isValid



prop_ComonadicVector_Eq_refl :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_Eq_refl v = v == v

prop_ComonadicVector_Eq_comm
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Eq_comm v w = (v == w) == (w == v)

prop_ComonadicVector_Eq_trans
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Eq_trans u v w = (u == v && v == w) `implies` (u == w)
    where a `implies` b = not a || b



prop_ComonadicVector_Ord_refl :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_Ord_refl v = compare v v == EQ

prop_ComonadicVector_Ord_comm
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Ord_comm v w = compare v w == inv (compare w v)
  where
    inv LT = GT
    inv EQ = EQ
    inv GT = LT

prop_ComonadicVector_Ord_trans
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Ord_trans u v w = istrans (compare u v)
                                               (compare v w)
                                               (compare u w)
  where
    istrans LT LT LT = True
    istrans LT EQ LT = True
    istrans LT GT _  = True
    istrans EQ LT LT = True
    istrans EQ EQ EQ = True
    istrans EQ GT GT = True
    istrans GT LT _  = True
    istrans GT EQ GT = True
    istrans GT GT GT = True
    istrans _  _  _  = False



prop_ComonadicVector_Show_Read :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_Show_Read v = read (show v) == v



prop_ComonadicVector_Unfoldable :: NonEmptyList Rational -> Bool
prop_ComonadicVector_Unfoldable (NonEmpty xs) = fmap toList v == Just xs
    where v = fromList xs :: Maybe (ComonadicVector V.Vector Rational)

prop_ComonadicVector_Foldable
    :: Fun (Rational, Rational) Rational
    -> Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Foldable (Fn f) x v =
    foldr (curry f) x v == foldr (curry f) x (toList v)



prop_ComonadicVector_Functor_id :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_Functor_id v = fmap id v == v

prop_ComonadicVector_Functor_compose
    :: Fun Rational Rational
    -> Fun Rational Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Functor_compose (Fn f) (Fn g) v =
    fmap (f . g) v == fmap f (fmap g v)



-- Traversable
-- Applicative
-- Distributive



prop_ComonadicVector_Comonad_unit_left
    :: Fun (ComonadicVector V.Vector Rational) Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Comonad_unit_left (Fn f) v = (extract =>= f) v == f v

prop_ComonadicVector_Comonad_unit_right
    :: Fun (ComonadicVector V.Vector Rational) Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Comonad_unit_right (Fn f) v = (f =>= extract) v == f v

prop_ComonadicVector_Comonad_assoc
    :: Fun (ComonadicVector V.Vector Rational) Rational
    -> Fun (ComonadicVector V.Vector Rational) Rational
    -> Fun (ComonadicVector V.Vector Rational) Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_Comonad_assoc (Fn f) (Fn g) (Fn h) v =
    ((f =>= g) =>= h) v == (f =>= (g =>= h)) v

-- ComonadApply

prop_ComonadicVector_ComonadStore_peek_pos
    :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_ComonadStore_peek_pos v = peek (pos v) v == extract v

prop_ComonadicVector_ComonadStore_pos_seek
    :: ComonadicVector V.Vector Rational -> Int -> Bool
prop_ComonadicVector_ComonadStore_pos_seek v i' = pos (seek i v) == i
    where i = i' `mod` length v



prop_ComonadicVector_neg_neg :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_neg_neg v = negateV (negateV v) == v

prop_ComonadicVector_add_inv :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_add_inv v = v ^+^ negateV v == zeroV *^ v

prop_ComonadicVector_add_zero
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_add_zero v w = v ^+^ zeroV *^ w == (const <$> v <*> w)

prop_ComonadicVector_add_comm
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_add_comm v w = v ^+^ w == w ^+^ v

prop_ComonadicVector_add_assoc
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_add_assoc u v w = (u ^+^ v) ^+^ w == u ^+^ (v ^+^ w)

prop_ComonadicVector_mul_inv :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_mul_inv v = (-1) *^ v == negateV v

prop_ComonadicVector_mul_comm
    :: Rational -> Rational -> ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_mul_comm a b v = (a * b) *^ v == b *^ (a *^ v)

prop_ComonadicVector_mul_assoc
    :: Rational -> Rational -> ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_mul_assoc a b v = (a * b) *^ v == a *^ (b *^ v)

prop_ComonadicVector_mul_add_distrib
    :: Rational
    -> ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_mul_add_distrib a v w =
    a *^ (v ^+^ w) == a *^ v ^+^ a *^ w

prop_ComonadicVector_dot_nonneg :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_dot_nonneg v = v <.> v >= zeroV

prop_ComonadicVector_dot_zero :: ComonadicVector V.Vector Rational -> Bool
prop_ComonadicVector_dot_zero v = z <.> z == zeroV where z = zeroV *^ v

prop_ComonadicVector_dot_comm
    :: ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_dot_comm v w = v <.> w == w <.> v

prop_ComonadicVector_dot_lin
    :: Rational
    -> ComonadicVector V.Vector Rational
    -> ComonadicVector V.Vector Rational
    -> Bool
prop_ComonadicVector_dot_lin a v w = a * (v <.> w) == v <.> (a *^ w)
