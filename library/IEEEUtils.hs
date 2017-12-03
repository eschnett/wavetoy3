-- | Utilities involving IEEE floating-point numbers, in particular
-- for approximate floating-point comparisons
module IEEEUtils
    ( (~==), (~<), (~>), (~/=), (~<=), (~>=)
    , Acc(..)
    , (~~)
    ) where

import Numeric.IEEE



infixl 4 ~~
infixl 4 ~==, ~<, ~>, ~/=, ~<=, ~>=



-- | An approximate comparison
data ApproxCmp a = ApproxCmp
    { _left, _right :: a
    , _comp :: Ordering -> Bool
    }

-- | approximately equal
(~==) :: a -> a -> ApproxCmp a
x ~== y = ApproxCmp x y (== EQ)

-- | approximately less than
(~<) :: a -> a -> ApproxCmp a
x ~< y = ApproxCmp x y (== LT)

-- | approximately greater than
(~>) :: a -> a -> ApproxCmp a
x ~> y = ApproxCmp x y (== GT)

-- | approximately not equal
(~/=) :: a -> a -> ApproxCmp a
x ~/= y = ApproxCmp x y (/= EQ)

-- | approximately less than or equal
(~<=) :: a -> a -> ApproxCmp a
x ~<= y = ApproxCmp x y (/= GT)

-- | approximately greater than or equal
(~>=) :: a -> a -> ApproxCmp a
x ~>= y = ApproxCmp x y (/= LT)



-- | An accuracy specification, consisting of the relative @accuracy@
-- (in multiples of the floating-point epsilon) and a set of @scales@
-- (that set the scale for the relative accuracy)
data Acc a = Acc
    { _accuracy :: a
    , _scales :: [a]
    }
             deriving (Read, Show)

-- | Calculate the absolute scale
getScale :: (IEEE a, Num a) => Acc a -> a
getScale (Acc acc scales) = acc * epsilon * absMaximum scales
  where
    absMaximum :: (Foldable t, Functor t, Num a, Ord a) => t a -> a
    absMaximum = maximum . fmap abs



-- | Evaluate an approximate comparison with respect to a given accuracy.
--
-- Example usage: Compare the numbers @x@ and @y@, allowing a relative
-- error of @1 * epsilon@ compared to the scale set by @10@ and @x@:
--
-- @
-- eq :: Double -> Double -> Bool
-- eq x y = x ~== y ~~ Acc 1 [10, x]
-- @
(~~) :: (IEEE a, Num a, Ord a) => ApproxCmp a -> Acc a -> Bool
ApproxCmp x y comp ~~ acc = comp ord
  where
    ord | abs (x - y) <= scale = EQ
        | x < y                = LT
        | otherwise            = GT
    scale = getScale acc
