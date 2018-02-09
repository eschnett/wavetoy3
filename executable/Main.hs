import qualified SimpleEvol as S

main :: IO ()
main = putStrLn (show (simple 5 (sqrt 2)))



simple :: Int -> Double -> Double
simple n x =
    let u  = S.initial x
        us = iterate S.rk2 u
    in  S.norm2 (head (drop n us))



-- import qualified Example
-- 
-- main :: IO ()
-- main = Example.main
