{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module PLC1Spec where

import Control.Comonad
import Control.Comonad.Store
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.Proxy
import Data.Unfoldable
import Data.Validity
import Data.VectorSpace
import GHC.TypeLits
import Test.QuickCheck.Function

import Bounded1
import Function
import IEEEUtils
import PLC1
import Poly



type N = 5                      -- 11



prop_PLC1_valid :: PLC1 N Double Double -> Bool
prop_PLC1_valid = isValid



prop_PLC1_Eq_refl :: PLC1 N Rational Rational -> Bool
prop_PLC1_Eq_refl v = v == v

prop_PLC1_Eq_comm
    :: PLC1 N Rational Rational -> PLC1 N Rational Rational -> Bool
prop_PLC1_Eq_comm v w = (v == w) == (w == v)

prop_PLC1_Eq_trans
    :: PLC1 N Rational Rational
    -> PLC1 N Rational Rational
    -> PLC1 N Rational Rational
    -> Bool
prop_PLC1_Eq_trans u v w = (u == v && v == w) `implies` (u == w)
    where a `implies` b = not a || b



prop_PLC1_Ord_refl :: PLC1 N Rational Rational -> Bool
prop_PLC1_Ord_refl v = compare v v == EQ

prop_PLC1_Ord_comm
    :: PLC1 N Rational Rational -> PLC1 N Rational Rational -> Bool
prop_PLC1_Ord_comm v w = compare v w == inv (compare w v)
  where
    inv LT = GT
    inv EQ = EQ
    inv GT = LT

prop_PLC1_Ord_trans
    :: PLC1 N Rational Rational
    -> PLC1 N Rational Rational
    -> PLC1 N Rational Rational
    -> Bool
prop_PLC1_Ord_trans u v w = istrans (compare u v) (compare v w) (compare u w)
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



prop_PLC1_Show_Read :: PLC1 N Rational Rational -> Bool
prop_PLC1_Show_Read v = read (show v) == v



prop_PLC1_Unfoldable :: PLC1 N Rational Rational -> Bool
prop_PLC1_Unfoldable v = (toList <$> w) == Just xs
  where
    xs = toList v
    w  = fromList xs :: Maybe (PLC1 N Rational Rational)

prop_PLC1_Foldable
    :: Fun (Integer, Integer) Integer
    -> Integer
    -> PLC1 N Integer Integer
    -> Bool
prop_PLC1_Foldable (Fn f) x v =
    foldr (curry f) x v == foldr (curry f) x (toList v)



prop_PLC1_Functor_id :: PLC1 N Rational Rational -> Bool
prop_PLC1_Functor_id v = fmap id v == v

prop_PLC1_Functor_compose
    :: Fun Integer Integer
    -> Fun Integer Integer
    -> PLC1 N Integer Integer
    -> Bool
prop_PLC1_Functor_compose (Fn f) (Fn g) v = fmap (f . g) v == fmap f (fmap g v)

-- Traversable



prop_PLC1_Applicative_identity :: PLC1 N Integer Integer -> Bool
prop_PLC1_Applicative_identity v = (pure id <*> v) == v

-- prop_PLC1_Applicative_composition
--     :: Fun (PLC1 N Integer Integer) (PLC1 N Integer Integer)
--     -> Fun (PLC1 N Integer Integer) (PLC1 N Integer Integer)
--     -> PLC1 N Integer Integer
--     -> Bool
-- prop_PLC1_Applicative_composition (Fn f) (Fn g) v =
--     (pure (.) <*> f <*> g <*> v) == (f <*> (g <*> v))

prop_PLC1_Applicative_homomorphism
    :: Fun (PLC1 N Integer Integer) (PLC1 N Integer Integer)
    -> PLC1 N Integer Integer
    -> Bool
prop_PLC1_Applicative_homomorphism (Fn f) v = (pure' f <*> pure' v)
    == pure' (f v)
  where
    pure' :: a -> PLC1 N Integer a
    pure' = pure

-- prop_PLC1_Applicative_interchange
--     :: Fun (PLC1 N Integer Integer) (PLC1 N Integer Integer)
--     -> Integer
--     -> Bool
-- prop_PLC1_Applicative_interchange (Fn f) x =
--     (f <*> pure x) == (pure ($ x) <*> f)



-- Distributive



prop_PLC1_Comonad_unit_left
    :: Fun (PLC1 N Integer Integer) Integer -> PLC1 N Integer Integer -> Bool
prop_PLC1_Comonad_unit_left (Fn f) v = (extract =>= f) v == f v

prop_PLC1_Comonad_unit_right
    :: Fun (PLC1 N Integer Integer) Integer -> PLC1 N Integer Integer -> Bool
prop_PLC1_Comonad_unit_right (Fn f) v = (f =>= extract) v == f v

prop_PLC1_Comonad_assoc
    :: Fun (PLC1 N Integer Integer) Integer
    -> Fun (PLC1 N Integer Integer) Integer
    -> Fun (PLC1 N Integer Integer) Integer
    -> PLC1 N Integer Integer
    -> Bool
prop_PLC1_Comonad_assoc (Fn f) (Fn g) (Fn h) v =
    ((f =>= g) =>= h) v == (f =>= (g =>= h)) v

-- ComonadApply

prop_PLC1_ComonadStore_peek_pos :: PLC1 N Integer Integer -> Bool
prop_PLC1_ComonadStore_peek_pos v = peek (pos v) v == extract v

prop_PLC1_ComonadStore_pos_seek :: PLC1 N Integer Integer -> Int -> Bool
prop_PLC1_ComonadStore_pos_seek v i' = pos (seek i v) == i
    where i = i' `mod` length v



prop_PLC1_zero :: Bool
prop_PLC1_zero = getAll $ foldMap (All . (==zeroV)) z
    where z = zeroV :: PLC1 N Rational Rational

prop_PLC1_neg_neg :: PLC1 N Rational Rational -> Bool
prop_PLC1_neg_neg v = negateV (negateV v) == v

prop_PLC1_add_inv :: PLC1 N (Bounded1 Rational) Rational -> Bool
-- prop_PLC1_add_inv v = v ^+^ negateV v == zeroV *^ v
-- prop_PLC1_add_inv v = v ^+^ negateV v == zeroV
prop_PLC1_add_inv v = magnitudeSq (v ^+^ negateV v) == zeroV
-- prop_PLC1_add_inv v = getAll $ foldMap (All . (== zeroV)) (v ^+^ negateV v)

-- prop_PLC1_add_zero
--     :: PLC1 N Rational Rational -> PLC1 N Rational Rational -> Bool
-- prop_PLC1_add_zero v w = v ^+^ zeroV *^ w == (const <$> v <*> w)
prop_PLC1_add_zero :: PLC1 N Rational Rational -> Bool
prop_PLC1_add_zero v = v ^+^ zeroV == v

prop_PLC1_add_comm
    :: PLC1 N Rational Rational -> PLC1 N Rational Rational -> Bool
prop_PLC1_add_comm v w = v ^+^ w == w ^+^ v

prop_PLC1_add_assoc
    :: PLC1 N Rational Rational
    -> PLC1 N Rational Rational
    -> PLC1 N Rational Rational
    -> Bool
prop_PLC1_add_assoc u v w = (u ^+^ v) ^+^ w == u ^+^ (v ^+^ w)

prop_PLC1_mul_inv :: PLC1 N Rational Rational -> Bool
prop_PLC1_mul_inv v = (-1) *^ v == negateV v

prop_PLC1_mul_comm :: Rational -> Rational -> PLC1 N Rational Rational -> Bool
prop_PLC1_mul_comm a b v = (a * b) *^ v == b *^ (a *^ v)

prop_PLC1_mul_assoc :: Rational -> Rational -> PLC1 N Rational Rational -> Bool
prop_PLC1_mul_assoc a b v = (a * b) *^ v == a *^ (b *^ v)

prop_PLC1_mul_add_distrib
    :: Rational -> PLC1 N Rational Rational -> PLC1 N Rational Rational -> Bool
prop_PLC1_mul_add_distrib a v w = a *^ (v ^+^ w) == a *^ v ^+^ a *^ w

prop_PLC1_dot_nonneg :: PLC1 N (Bounded1 Rational) Rational -> Bool
prop_PLC1_dot_nonneg v = v <.> v >= zeroV

prop_PLC1_dot_zero :: PLC1 N (Bounded1 Rational) Rational -> Bool
prop_PLC1_dot_zero v = z <.> z == zeroV where z = zeroV *^ v

prop_PLC1_dot_comm
    :: PLC1 N (Bounded1 Rational) Rational
    -> PLC1 N (Bounded1 Rational) Rational
    -> Bool
prop_PLC1_dot_comm v w = v <.> w == w <.> v

prop_PLC1_dot_lin
    :: Rational
    -> PLC1 N (Bounded1 Rational) Rational
    -> PLC1 N (Bounded1 Rational) Rational
    -> Bool
prop_PLC1_dot_lin a v w = a * (v <.> w) == v <.> (a *^ w)



prop_PLC1_eval_zero :: Bounded1 Double -> Bool
prop_PLC1_eval_zero x =
    let f :: PLC1 N (Bounded1 Double) Double
        f = fromJust $ fromList $ replicate n 0
    in  eval f x == 0
    where n = fromInteger (natVal (Proxy :: Proxy N))

prop_PLC1_eval_const :: Double -> Bounded1 Double -> Bool
prop_PLC1_eval_const y x =
    let f :: PLC1 N (Bounded1 Double) Double
        f = fromJust $ fromList $ replicate n y
    in  eval f x ~== y ~~ Acc 1 [1, y]
    where n = fromInteger (natVal (Proxy :: Proxy N))

prop_PLC1_eval_id :: Bounded1 Double -> Bool
prop_PLC1_eval_id x =
    let
        f :: PLC1 N (Bounded1 Double) Double
        f = fromJust
            $ fromList [ (fromIntegral i - rx) / rx | i <- [0 .. n - 1] ]
    in
        eval f x ~== getBounded1 x ~~ Acc 10 [1, getBounded1 x]
  where
    n  = fromInteger (natVal (Proxy :: Proxy N)) :: Int
    rx = fromIntegral (n - 1) / 2

prop_PLC1_eval_Function :: Poly Double -> Bounded1 Double -> Bool
prop_PLC1_eval_Function poly x = f x ~== eval g x ~~ acc
  where
    f :: Bounded1 Double -> Double
    f = evalPoly poly . getBounded1
    g :: PLC1 N (Bounded1 Double) Double
    g   = discretized f
    acc = Acc 10e15 $ fmap getBounded1 [minBound, maxBound] ++ polyCoeffs poly
