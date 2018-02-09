{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Subcategory5 where

import Prelude hiding (Functor(..))
import qualified Prelude as P

import Data.Constraint
import Data.Kind
import GHC.Generics



class Category (k :: Type -> Type -> Type) where
    type Ok k a :: Constraint
    id :: Ok k a => k a a
    (.) :: (Ok k a, Ok k b, Ok k c) => k b c -> k a b -> k a c

class (Category (Dom f), Category (Cod f)) => Functor (f :: Type -> Type) where
    type Dom f :: Type -> Type -> Type
    type Cod f :: Type -> Type -> Type
    cmap :: Ok (Dom f) a :- Ok (Cod f) (f a)
    fmap :: (Ok (Dom f) a, Ok (Dom f) b) => Dom f a b -> Cod f (f a) (f b)



newtype (.->) a b = NFun { runNFun :: a -> b }
instance Category (.->) where
    type Ok (.->) a = Num a
    id = NFun P.id
    NFun f . NFun g = NFun (f P.. g)

newtype NIdentity a = NIdentity a
    deriving (Eq, Ord, Read, Show, Num)

instance Functor NIdentity where
    type Dom NIdentity = (.->)
    type Cod NIdentity = (.->)
    cmap = Sub Dict
    fmap (NFun f) = NFun $ \(NIdentity x) -> NIdentity (f x)

-- class Num1 (f :: Type -> Type) where
--     num1 :: (Num a, Num1 f) :- Num (f a)
instance (Num (f a), Num (g a)) => Num ((f :*:g) a) where
    (xs :*: xs') + (ys :*: ys') = (xs + ys) :*: (xs' + ys')
-- instance (Num1 f, Num1 g) => Num1 (f :*:g) where
--     num1 = Sub Dict
instance (Functor f, Functor g,
          Dom f ~ (.->), Dom g ~ (.->),
          Cod f ~ (.->), Cod g ~ (.->))
        => Functor (f :*: g) where
    type Dom (f :*: g) = (.->)
    type Cod (f :*: g) = (.->)
    -- cmap = cmap @ f &&& cmap @ g
    cmap = undefined
    fmap f = NFun $ \(xs :*: ys) -> runNFun (fmap f) xs :*: runNFun (fmap f) ys
