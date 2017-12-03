{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Integration
  ( integrate
  ) where

import Data.VectorSpace

-- import Numeric.Integration.TanhSinh
import Numeric.Integration.VectorSpace.TanhSinh

-- integrate :: (RealFrac a, RealFrac b) => (a -> b) -> a -> a -> b
-- integrate f lo hi = realToFrac $ result $ last $ simpson f' lo' hi'
--     where f' = realToFrac . f . realToFrac
--           lo' = realToFrac lo
--           hi' = realToFrac hi
integrate
  :: (RealFrac a, InnerSpace b, Floating (Scalar b), Ord (Scalar b))
  => (a -> b)
  -> a
  -> a
  -> b
integrate f lo hi = result $ last $ simpson f' lo' hi'
 where
  f'  = f . realToFrac
  lo' = realToFrac lo
  hi' = realToFrac hi
