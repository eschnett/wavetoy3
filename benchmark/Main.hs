import Criterion.Main

import qualified SimpleEvol as S

main :: IO ()
main = defaultMain [bench "SimpleEvol" (whnf (simple 1) 0)]



simple :: Int -> Double -> Double
simple n x =
    let u  = S.initial x
        us = iterate S.rk2 u
    in  S.norm2 (head (drop n us))
