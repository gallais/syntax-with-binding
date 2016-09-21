{-# OPTIONS -Wall                  #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Examples where

import GHC.TypeLits
import Data.Void

import Utils
import Generic
import Syntaxes

-------------------------------------------------------------
-- OPEN TERMS WITH N FREE VARIABLES
-------------------------------------------------------------

type family Free (n :: Nat) :: * where
  Free 0 = Void
  Free n = Maybe (Free (n - 1))

type OTerm n = Term (Free n)

-------------------------------------------------------------
-- EXAMPLES FOR TmF
-------------------------------------------------------------

oTERM :: OTerm 1
oTERM = TmL' $ MkVar $ Just Nothing

oTERM' :: OTerm 2
oTERM' = rename oTERM (fmap Just)

idTERM :: Term Void
idTERM = TmL' $ MkVar Nothing

falseTERM :: Term Void
falseTERM = subst oTERM $ maybe idTERM absurd . runVariable

cutTERM :: Term Void
cutTERM = TmA falseTERM falseTERM -- (\ x y -> y) (\ x y -> y) ---->* (\ y -> y)

normTERM :: Term Void
normTERM = norm cutTERM

-------------------------------------------------------------
-- EXAMPLES FOR CLF
-------------------------------------------------------------

ones :: CList Integer
ones = CList $ CLCON' 1 $ Var Z

ones' :: [Integer]
ones' = take 10 $ toStream ones

twothrees :: CList Integer
twothrees = CList $ CLCON' 2 $ CLCON' 3 $ Var $ S Z

twothrees' :: [Integer]
twothrees' = take 10 $ toStream twothrees

threefours :: CList Integer
threefours = fmap (+1) twothrees

threefours' :: [Integer]
threefours' = take 10 $ toStream threefours

-------------------------------------------------------------
-- EXAMPLES FOR YF
-------------------------------------------------------------

yFalse :: YTM 'Zero
yFalse = Y $ Var Z

yFalse' :: YTM 'Zero
yFalse' = Fix $ YA yFalse yFalse

yFalse'' :: YTM 'Zero
yFalse'' = norm yFalse'
