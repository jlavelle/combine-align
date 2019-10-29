{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE KindSignatures #-}

module Lib where

import           Control.Applicative
import           Data.Bifunctor                 ( bimap )
import           Data.Coerce
import           Data.Either                    ( lefts
                                                , rights
                                                )
import           Data.Foldable                  ( toList )
import           Data.Functor.Alt
import           Data.Functor.Apply
import           Data.Functor.Identity
import           Data.Kind
import qualified Data.Map                      as M
import           Data.Proxy
import qualified Data.Semialign                as S
import           Data.These                     ( These(..)
                                                , these
                                                )
import qualified Data.Tree                     as T
import qualified Hedgehog                      as H
import qualified Hedgehog.Gen                  as Gen
import qualified Hedgehog.Range                as Range

newtype ZipTree a = ZipTree { runZipTree :: T.Tree a }
  deriving (Show, Functor, Eq)

instance Alt ZipTree where
  ZipTree (T.Node x xs) <!> ZipTree (T.Node _ ys) = ZipTree $ T.Node x $ go
    xs
    ys
   where
    go []       []       = []
    go xs       []       = xs
    go []       ys       = ys
    go (x : xs) (y : ys) = (runZipTree (ZipTree x <!> ZipTree y)) : go xs ys

instance Apply ZipTree where
  liftF2 f (ZipTree (T.Node x xs)) (ZipTree (T.Node y ys)) = ZipTree
    $ T.Node (f x y) go
   where
    go =
      runZipTree <$> zipWith (\x y -> liftF2 f (ZipTree x) (ZipTree y)) xs ys

combineTree :: T.Tree a -> T.Tree b -> T.Tree (These a b)
combineTree (T.Node x xs) (T.Node y ys) = T.Node (These x y) (go xs ys)
 where
  go []       []       = []
  go xs       []       = fmap (fmap This) xs
  go []       ys       = fmap (fmap That) ys
  go (x : xs) (y : ys) = combineTree x y : go xs ys

newtype GoodBoyList a = GB [a]
  deriving (Functor, Eq, Show)
  deriving Apply via (WrappedApplicative ZipList)
  deriving Filterable via []
  deriving Semigroup via [a]
  deriving Foldable via []

deriving via (WrappedApplicative ZipList) instance Alt GoodBoyList

newtype I a = I { runI :: a }
  deriving Show
  deriving Functor via Identity
  deriving Apply via (WrappedApplicative Identity)

instance Alt I where
  I a <!> I b = I a

newtype AltApply f a = AltApply { runAltApply :: f a }
  deriving (Functor, Apply, Show)

instance Alt f => Alt (AltApply f) where
  AltApply a <!> AltApply b = AltApply $ a <!> b

instance (Alt f, Apply f) => S.Semialign (AltApply f) where
  align = combine
  zip   = liftF2 (,)

union :: Alt f => f a -> f b -> f (Either a b)
union a b = (Left <$> a) <!> (Right <$> b)

mkThese :: Either (a, b) (Either a b) -> These a b
mkThese = either (uncurry These) (either This That)

combine :: (Apply f, Alt f) => f a -> f b -> f (These a b)
combine a b = mkThese <$> union (liftF2 (,) a b) (union a b)

zipC :: (Apply f, Alt f, Filterable f) => f a -> f b -> f (a, b)
zipC a b = fst $ partition $ mkEither <$> combine a b

liftF2C :: (Apply f, Alt f, Filterable f) => (a -> b -> c) -> f a -> f b -> f c
liftF2C f a b = fmap (uncurry f $) $ zipC a b

unionC :: (Apply f, Alt f, Filterable f) => f a -> f b -> f (Either a b)
unionC a b = fmap (either (Left . uncurry const) id . mkEither) $ combine a b

mapMaybe :: Filterable f => (a -> Maybe b) -> f a -> f b
mapMaybe f = snd . partition . fmap (maybe (Left ()) Right . f)

class Functor f => Filterable f where
  partition :: f (Either a b) -> (f a, f b)

instance Filterable [] where
  partition xs = (lefts xs, rights xs)

mkEither :: These a b -> Either (a, b) (Either a b)
mkEither = these (Right . Left) (Right . Right) (\a b -> Left (a, b))

destruct :: (Apply f, Filterable f) => f (These a b) -> (f a, f a)
destruct f =
  let (a, b) = partition $ mkEither <$> f
      (c, _) = partition b
  in  (fmap fst a, c)

foldableLaw
  :: (Eq a, Foldable f, Apply f, Alt f, Filterable f) => f a -> f b -> Bool
foldableLaw x y =
  (uncurry (<>) $ bimap toList toList $ destruct $ combine x y) == toList x

genTree :: H.Gen a -> H.Gen (T.Tree a)
genTree ga = T.Node <$> ga <*> Gen.recursive
  Gen.choice
  [Gen.constant []]
  [Gen.list (Range.linear 0 10) (genTree ga)]

genZipTree :: H.Gen a -> H.Gen (ZipTree a)
genZipTree = fmap ZipTree . genTree

genZipList :: H.Gen a -> H.Gen (ZipList a)
genZipList g = ZipList <$> Gen.list (Range.linear 0 10) g

intGen :: Int -> Int -> H.Gen Int
intGen a b = Gen.integral $ Range.constant a b

type AlignCtx f g a
  = ( Coercible g f
    , Eq (f (These a a))
    , Show (f (These a a))
    , S.Semialign f
    , Show (f a)
    , Apply g
    , Alt g
    )

prop_combine_align
  :: forall  g f a . AlignCtx f g a => Proxy g -> H.Gen (f a) -> H.Property
prop_combine_align _ g = H.property $ do
  x <- H.forAll g
  y <- H.forAll g
  S.align x y
    H.=== (coerce (combine (coerce x :: g a) (coerce y :: g a)) :: f (These a a)
          )

zipA :: Apply f => f a -> f b -> f (a, b)
zipA = liftF2 (,)

unzipF :: Functor f => f (a, b) -> (f a, f b)
unzipF f = (fmap fst f, fmap snd f)

type HCtx f a = (Show (f a), Eq (f a))

prop_strong_apply1
  :: (Apply f, HCtx f a, Monad m) => H.Gen (f a) -> H.PropertyT m ()
prop_strong_apply1 g = do
  x <- H.forAll g
  unzipF (zipA x x) H.=== (x, x)

prop_strong_apply2
  :: (Apply f, HCtx f (a, b), Monad m) => H.Gen (f (a, b)) -> H.PropertyT m ()
prop_strong_apply2 g = do
  x <- H.forAll g
  uncurry zipA (unzipF x) H.=== x

prop_strong_apply
  :: (Apply f, forall  x . Eq x => Eq (f x), forall  x . Show x => Show (f x))
  => (forall a . H.Gen a -> H.Gen (f a))
  -> H.Property
prop_strong_apply mkg = H.property $ do
  let g1 = mkg $ intGen 0 10
      g2 = mkg $ (,) <$> intGen 0 10 <*> intGen 0 10
  prop_strong_apply1 g1
  prop_strong_apply2 g2

prop_strong_apply_ziptree :: H.Property
prop_strong_apply_ziptree = prop_strong_apply genZipTree

prop_strong_apply_ziplist :: H.Property
prop_strong_apply_ziplist = prop_strong_apply genZipList

someFunc :: IO ()
someFunc = putStrLn "someFunc"
