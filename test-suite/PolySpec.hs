module PolySpec where

import Poly



prop_Poly_eval :: Rational -> Bool
prop_Poly_eval x = evalPoly (Poly [1, 2, 3]) x == 1 + x * (2 + x * 3)

prop_Poly_int :: Bool
prop_Poly_int = intPoly (Poly [1 :: Rational, 2, 3]) == Poly [0, 1, 1, 1]
