{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module CategoryC where

import Data.Functor.Compose
import Data.Functor.Identity
import Data.Kind



--------------------------------------------------------------------------------



class CategoryC (cat :: k -> Constraint) where
    type IdentityC :: k
    type ComposeC :: k -> k -> k

instance CategoryC Functor where
    type IdentityC = Identity
    type ComposeC = Compose



--------------------------------------------------------------------------------



-- data Fun (c :: (Type -> Type -> Type) -> Constraint) a b =
--     Fun (forall (r :: Type -> Type -> Type). c r => r a b)

newtype Fun a b = Fun (forall r. Repr r => r a b)

class Repr r where
    hask :: r a b -> a -> b
