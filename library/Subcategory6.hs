{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Subcategory6 where

import Prelude hiding (Functor(..))
import qualified Prelude as P

import Data.Constraint
import Data.Kind
import GHC.Generics



class Category (ok :: Type -> Constraint) (k :: Type -> Type -> Type) where
    id :: ok a => k a a
    (.) :: (ok a, ok b, ok c) => k b c -> k a b -> k a c

class (Category ok m, Category ok' m') => Functor ok m ok' m' (f :: Type -> Type) where
    cmap :: ok a :- ok' (f a)
    fmap :: (ok a, ok b) => m a b -> m' (f a) (f b)



-- newtype (.->) a b = NFun { runNFun :: a -> b }
-- instance Category (.->) where
--     type Ok (.->) a = Num a
--     id = NFun P.id
--     NFun f . NFun g = NFun (f P.. g)
-- 
-- newtype NIdentity a = NIdentity a
--     deriving (Eq, Ord, Read, Show, Num)
-- 
-- instance Functor NIdentity where
--     type Dom NIdentity = (.->)
--     type Cod NIdentity = (.->)
--     cmap = Sub Dict
--     fmap (NFun f) = NFun $ \(NIdentity x) -> NIdentity (f x)
-- 
-- -- class Num1 (f :: Type -> Type) where
-- --     num1 :: (Num a, Num1 f) :- Num (f a)
-- instance (Num (f a), Num (g a)) => Num ((f :*:g) a) where
--     (xs :*: xs') + (ys :*: ys') = (xs + ys) :*: (xs' + ys')
-- -- instance (Num1 f, Num1 g) => Num1 (f :*:g) where
-- --     num1 = Sub Dict
-- instance (Functor f, Functor g,
--           Dom f ~ (.->), Dom g ~ (.->),
--           Cod f ~ (.->), Cod g ~ (.->))
--         => Functor (f :*: g) where
--     type Dom (f :*: g) = (.->)
--     type Cod (f :*: g) = (.->)
--     -- cmap = let cmapf = cmap @ f
--     --            cmapg = cmap @ g
--     --        in cmapf &&& cmapg
--     cmap = cmap @ f &&& cmap @ g
--     fmap f = NFun $ \(xs :*: ys) -> runNFun (fmap f) xs :*: runNFun (fmap f) ys
