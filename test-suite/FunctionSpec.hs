{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module FunctionSpec where

import Control.Category
import Data.Either.Combinators (swapEither)
import Data.Tuple.Extra ((&&&), swap)
import Prelude hiding ((.))
import Test.QuickCheck.Function

import Bounded1
import Function
import IEEEUtils



prop_FIdentity_id :: Rational -> Bool
prop_FIdentity_id x = eval FIdentity x == x

prop_FIdentity_int :: FIdentity (Bounded1 Rational) (Bounded1 Rational) -> Bool
prop_FIdentity_int f = integral f == maxBound - minBound



prop_FCompose_dot
    :: Fun Rational Rational -> Fun Rational Rational -> Rational -> Bool
prop_FCompose_dot (Fn f) (Fn g) x = eval (FCompose f g) x == (f . g) x

prop_FCompose_assoc
    :: Fun Rational Rational
    -> Fun Rational Rational
    -> Fun Rational Rational
    -> Rational
    -> Bool
prop_FCompose_assoc (Fn f) (Fn g) (Fn h) x =
    eval (FCompose (FCompose f g) h) x == eval (FCompose f (FCompose g h)) x



prop_FProd_pair
    :: Fun Rational Rational -> Fun Rational Rational -> Rational -> Bool
prop_FProd_pair (Fn f) (Fn g) x = eval (FProd f g) x == (f &&& g) x

prop_FProd_comm
    :: Fun Rational Rational -> Fun Rational Rational -> Rational -> Bool
prop_FProd_comm (Fn f) (Fn g) w =
    swap (eval (FProd f g) w) == eval (FProd g f) w

prop_FProd_assoc
    :: Fun Rational Rational
    -> Fun Rational Rational
    -> Fun Rational Rational
    -> Rational
    -> Bool
prop_FProd_assoc (Fn f) (Fn g) (Fn h) w =
    assoc (eval (FProd (FProd f g) h) w) == eval (FProd f (FProd g h)) w
    where assoc ((x, y), z) = (x, (y, z))



prop_FPSum_either
    :: Fun Rational Rational
    -> Fun Rational Rational
    -> Either Rational Rational
    -> Bool
prop_FPSum_either (Fn f) (Fn g) x = eval (FSum f g) x == either f g x

prop_FSum_comm
    :: Fun Rational Rational
    -> Fun Rational Rational
    -> Either Rational Rational
    -> Bool
prop_FSum_comm (Fn f) (Fn g) w =
    eval (FSum f g) w == eval (FSum g f) (swapEither w)

prop_FSum_assoc
    :: Fun Rational Rational
    -> Fun Rational Rational
    -> Fun Rational Rational
    -> Either (Either Rational Rational) Rational
    -> Bool
prop_FSum_assoc (Fn f) (Fn g) (Fn h) w = eval (FSum (FSum f g) h) w
    == eval (FSum f (FSum g h)) (assocEither w)
  where
    assocEither (Left  (Left  x)) = Left x
    assocEither (Left  (Right x)) = Right (Left x)
    assocEither (Right x        ) = Right (Right x)



prop_FProd_FSum_distrib
    :: Fun Rational Rational
    -> Fun Rational Rational
    -> Fun Rational Rational
    -> Either Rational Rational
    -> Bool
prop_FProd_FSum_distrib (Fn f) (Fn g) (Fn h) w =
    eval (FProd (f . bothEither) (FSum g h)) w
        == eval (FSum (FProd f g) (FProd f h)) w
  where
    bothEither (Left  x) = x
    bothEither (Right x) = x



prop_FCurry_eval
    :: Fun (Rational, Rational) Rational -> Rational -> Rational -> Bool
prop_FCurry_eval (Fn f) v w = eval2 (FCurry f) v w == curry f v w
    where eval2 g x y = eval (eval g x) y

prop_FCurry_inv
    :: Fun (Rational, Rational) Rational -> (Rational, Rational) -> Bool
prop_FCurry_inv (Fn f) w = eval (FUncurry (eval2 (FCurry f))) w == f w
    where eval2 g x y = eval (eval g x) y

-- QuickCheck apparently cannot generate curried functions. Thus we
-- generate an uncurried one, and then curry it.
prop_FUncurry_eval
    :: Fun (Rational, Rational) Rational -> (Rational, Rational) -> Bool
prop_FUncurry_eval (Fn f) w = eval (FUncurry (curry f)) w == f w

prop_FUncurry_inv
    :: Fun (Rational, Rational) Rational -> Rational -> Rational -> Bool
prop_FUncurry_inv (Fn f) v w =
    eval2 (FCurry (eval (FUncurry (curry f)))) v w == curry f v w
    where eval2 g x y = eval (eval g x) y



prop_Hask_zero_int :: Bool
prop_Hask_zero_int =
    integral (const 0 :: Bounded1 Double -> Bounded1 Double) == 0

prop_Hask_one_int :: Bool
prop_Hask_one_int =
    integral (const 1 :: Bounded1 Double -> Bounded1 Double) ~== 2 ~~ acc
    where acc = Acc 1000 [minBound, maxBound, 2]

prop_Hask_const_int :: Bounded1 Double -> Bool
prop_Hask_const_int x =
    integral (const x :: Bounded1 Double -> Bounded1 Double) ~== 2 * x ~~ acc
    where acc = Acc 1000 [minBound, maxBound, 2 * x]

prop_Hask_poly_int :: [Bounded1 Double] -> Bool
prop_Hask_poly_int coeffs = integral fun ~== bnds ifun ~~ acc
  where
    poly :: Num a => [a] -> a -> a
    poly []     _ = 0
    poly (c:cs) x = c + x * poly cs x
    icoeffs = 0 : [ c / Bounded1 n |    c <- coeffs | n <- [1..] ]
    fun     = poly coeffs
    ifun    = poly icoeffs
    bnds f = f maxBound - f minBound
    acc = Acc 1000 [minBound, maxBound, fun minBound, fun maxBound]



{-# ANN module "HLint: ignore Eta reduce" #-}
