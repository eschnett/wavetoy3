{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module SubcategorySpec where

import Data.Proxy
import Test.QuickCheck
import Test.QuickCheck.Function
-- import Test.QuickCheck.Instances
import Prelude as P

import Subcategory as S



instance Arbitrary1 Proxy where
    liftArbitrary _ = P.pure Proxy
    liftShrink _ _ = []

instance Arbitrary (Proxy a) where
    arbitrary = P.pure Proxy
    shrink _  = []

instance CoArbitrary (Proxy a) where
    coarbitrary _ = id

instance Function (Proxy a) where
    function = functionMap (const ()) (const Proxy)



prop_Subcategory_List_Functor_id :: [Int] -> Property
prop_Subcategory_List_Functor_id = prop_Functor_id

prop_Subcategory_List_Functor_comp ::
    Fun Int Int -> Fun Int Int -> [Int] -> Property
prop_Subcategory_List_Functor_comp (Fn f) (Fn g) = prop_Functor_comp f g

prop_Subcategory_List_Functor_Id :: Fun Int Int -> Int -> Property
prop_Subcategory_List_Functor_Id (Fn f) = prop_Functor_Id f

prop_Subcategory_List_Functor_Comp :: Fun Int Int -> [[Int]] -> Property
prop_Subcategory_List_Functor_Comp (Fn f) = prop_Functor_Comp f

prop_Subcategory_List_Apply_assoc :: [Int] -> [Int] -> [Int] -> Property
prop_Subcategory_List_Apply_assoc = prop_Apply_assoc

prop_Subcategory_List_Apply_fmap_inner ::
    Fun Int Int -> [Int] -> [Int] -> Property
prop_Subcategory_List_Apply_fmap_inner (Fn f) = prop_Apply_fmap_inner f

prop_Subcategory_List_Apply_fmap_outer ::
    Fun (Int, Int) Int -> [Int] -> [Int] -> Property
prop_Subcategory_List_Apply_fmap_outer (Fn f) = prop_Apply_fmap_outer f

prop_Subcategory_List_Applicative_id :: Int -> [Int] -> Property
prop_Subcategory_List_Applicative_id = prop_Applicative_id

-- prop_Subcategory_List_Applicative_comp ::
--     [Fun Int Int] -> [Fun Int Int] -> [Int] -> Property
-- prop_Subcategory_List_Applicative_comp f g =
--     S.prop_Applicative_comp (map apply f) (map apply g)
-- 
-- prop_Subcategory_List_Applicative_homo ::
--     Proxy [] -> Fun Int Int -> Int -> Property
-- prop_Subcategory_List_Applicative_homo proxy (Fn f) =
--     S.prop_Applicative_homo proxy f
-- 
-- prop_Subcategory_List_Applicative_interchange ::
--     [Fun Int Int] -> Int -> Property
-- prop_Subcategory_List_Applicative_interchange f =
--     S.prop_Applicative_interchange (map apply f)

prop_Subcategory_List_Traversable_id :: [Int] -> Property
prop_Subcategory_List_Traversable_id = prop_Traversable_id

prop_Subcategory_List_Traversable_comp
    :: Fun Int (Maybe Int)
    -> Fun Int (Either Int Int)
    -> [Int]
    -> Property
prop_Subcategory_List_Traversable_comp (Fn f) (Fn g) = prop_Traversable_comp f g



prop_Subcategory_CVector_Functor_id :: CVector 10 Int -> Property
prop_Subcategory_CVector_Functor_id = prop_Functor_id

prop_Subcategory_CVector_Functor_comp
    :: Fun Int Int -> Fun Int Int -> CVector 10 Int -> Property
prop_Subcategory_CVector_Functor_comp (Fn f) (Fn g) = prop_Functor_comp f g

prop_Subcategory_CVector_Apply_assoc ::
    CVector 10 Int -> CVector 10 Int -> CVector 10 Int -> Property
prop_Subcategory_CVector_Apply_assoc = prop_Apply_assoc

prop_Subcategory_CVector_Apply_fmap_inner ::
    Fun Int Int -> CVector 10 Int -> CVector 10 Int -> Property
prop_Subcategory_CVector_Apply_fmap_inner (Fn f) = prop_Apply_fmap_inner f

prop_Subcategory_CVector_Apply_fmap_outer ::
    Fun (Int, Int) Int -> CVector 10 Int -> CVector 10 Int -> Property
prop_Subcategory_CVector_Apply_fmap_outer (Fn f) = prop_Apply_fmap_outer f
