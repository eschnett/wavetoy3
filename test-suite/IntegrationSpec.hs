module IntegrationSpec where

import Bounded1
import IEEEUtils
import Integration
import Poly



prop_integrate_zero :: Bool
prop_integrate_zero =
    integrate (const 0) minBound (maxBound :: Bounded1 Double)
        == (0 :: Bounded1 Double)

prop_integrate_one :: Bool
prop_integrate_one =
    integrate (const 1) minBound (maxBound :: Bounded1 Double)
        ~== (2 :: Bounded1 Double)
        ~~  acc
    where acc = Acc 1000 [minBound, maxBound, 2]

prop_integrate_const :: Bounded1 Double -> Bool
prop_integrate_const x =
    integrate (const x) minBound (maxBound :: Bounded1 Double) ~== 2 * x ~~ acc
    where acc = Acc 1000 [minBound, maxBound, 2 * x]

prop_integrate_Poly :: [Bounded1 Double] -> Bool
prop_integrate_Poly coeffs =
    integrate f minBound maxBound ~== (intf maxBound - intf minBound) ~~ acc
  where
    poly    = Poly coeffs
    intpoly = intPoly poly
    f       = evalPoly poly
    intf    = evalPoly intpoly
    acc =
        Acc 10000 ([minBound, maxBound, intf minBound, intf maxBound] ++ coeffs)
