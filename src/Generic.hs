{-# OPTIONS -Wall                   #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}

module Generic where

import Data.Functor.Classes
import Data.Proxy
import Control.Monad.State

import Utils
import Scopes

-------------------------------------------------------------
-- SYNTAX WITH BINDING
-------------------------------------------------------------

-- This is what I'd like to write:
-- kind Scoped  = * -> *
-- kind ScopedT = Scoped -> Scoped
-- kind Syntax  = ScopedT -> Scoped
-- kind SyntaxT = Syntax -> Syntax
-- class SyntaxWithBinding (syn :: SyntaxT) where

class SyntaxWithBinding
      (syn :: (((i -> *) -> (i -> *)) -> (i -> *))
           ->  ((i -> *) -> (i -> *)) -> (i -> *)) where
  reindex :: (rec scp a -> rec' scp' a')
          -> (scp (rec scp) a -> scp' (rec' scp') a')
          -> syn rec scp a -> syn rec' scp' a'


-------------------------------------------------------------
-- FIXPOINT OF A SYNTAX TRANSFORMER
-------------------------------------------------------------

data Fix (v :: i -> *) f (s :: (i -> *) -> (i -> *)) (a :: i) :: * where
   Var :: v a             -> Fix v f s a
   Fix :: f (Fix v f) s a -> Fix v f s a

type Fix' = Fix Variable
type Syntax j t = Fix j t (Scope j)

pattern MkVar a = Var (Variable a)

instance (Eq1 v, Eq1 (f (Fix v f) s)) => Eq1 (Fix v f s) where
  Var v `eq1` Var w = v `eq1` w
  Fix t `eq1` Fix u = t `eq1` u
  _     `eq1` _     = False
instance (Eq1 v, Eq1 (f (Fix v f) s), Eq a) => Eq (Fix v f s a) where
  (==) = eq1

instance (Show1 v, Show1 (f (Fix v f) s)) => Show1 (Fix v f s) where
  showsPrec1 i e = case e of
    Var v -> showString "Var " . showsPrec1 (1+i) v
    Fix t -> showString "Fix " . showsPrec1 (1+i) t
deriving instance (Show (v a), Show (f (Fix v f) s a)) => Show (Fix v f s a)

-------------------------------------------------------------
-- ALGEBRAS, EVALUATION AND FUNDAMENTAL LEMMA OF SYNTAXES
-------------------------------------------------------------

class Alg j t e v where
  alg :: Proxy j -> t (Const v) (Kripke j e) a -> v a
  ret :: Proxy j -> Proxy t -> e ~> v

class Eval j t e v where
  eval  :: (j a -> e b) -> t a -> v b
  eval' :: Proxy e -> (j a -> e b) -> t a -> v b
  eval' _ = eval

instance (VarLike j, HigherFunctor j e, SyntaxWithBinding t, Alg j t e v) => Eval j (Syntax j t) e v where
  eval = go where

    go :: forall a b. (j a -> e b) -> Syntax j t a -> v b
    go rho (Var a) = ret (Proxy :: Proxy j) (Proxy :: Proxy t) $ rho a
    go rho (Fix t) = alg (Proxy :: Proxy j)
                         $ reindex (Const . go rho)
                                   (\ b -> Kripke $ \ i e ->
                                             (Const . go (inspect e (hfmap i . rho)))
                                             $ runScope b)
                                   t

-------------------------------------------------------------
-- RENAMING
-------------------------------------------------------------

instance (VarLike j, SyntaxWithBinding t) => Alg j t j (Syntax j t) where
  ret _ _ = Var
  alg _ = Fix . reindex runConst (abstract' id)

rename :: (VarLike j, HigherFunctor j j, SyntaxWithBinding t) =>
          Syntax j t a -> (j a -> j b) -> Syntax j t b
rename = flip $ eval' (Proxy :: Proxy j)

instance (VarLike j, HigherFunctor j j, SyntaxWithBinding t) => HigherFunctor j (Syntax j t) where
  hfmap = flip rename

-------------------------------------------------------------
-- Substitution
-------------------------------------------------------------

instance (VarLike j, SyntaxWithBinding t) => Alg j t (Syntax j t) (Syntax j t) where
  ret _ _ = id
  alg _ = Fix . reindex runConst (abstract' Var)

subst :: (VarLike j, HigherFunctor j j, SyntaxWithBinding t) =>
         Syntax j t a -> (j a -> Syntax j t b) -> Syntax j t b
subst = flip eval

instance (VarLike j, HigherFunctor j j, SyntaxWithBinding t) => RelativeMonad j (Syntax j t) where
  rreturn = Var
  rbind   = subst

-------------------------------------------------------------
-- MODEL OF A SYNTAXT AND NORMALISATION BY EVALUTION
-------------------------------------------------------------

newtype Model v f a = Model { runModel :: Fix v f (Kripke v (Model v f)) a }

instance SyntaxWithBinding f => HigherFunctor j (Fix j f (Kripke j (Model j f))) where
  hfmap f e = case e of
      Var a  -> Var $ f a
      Fix e' -> Fix $ reindex (hfmap f) (hfmap f) e'

instance HigherFunctor j (Fix j f (Kripke j (Model j f))) =>
         HigherFunctor j (Model j f) where
  hfmap f (Model m) = Model (hfmap f m)

type Model' = Model Variable

reflect :: j ~> Model j f
reflect = Model . Var

reify :: forall f j. (VarLike j, SyntaxWithBinding f) => Model j f ~> Syntax j f
reify = go . runModel where

  go :: Fix j f (Kripke j (Model j f)) ~> Syntax j f
  go (Var a) = Var a
  go (Fix f) = Fix $ reindex go (scope go . abstract reflect) f

norm ::
  forall j t. (VarLike j,  HigherFunctor j (Model j t), SyntaxWithBinding t)
         => Alg j t (Model j t) (Model j t)
         => Syntax j t ~> Syntax j t
norm = reify . eval' (Proxy :: Proxy (Model j t)) reflect


-------------------------------------------------------------
-- DISPLAY USING A NAME SUPPLY
-------------------------------------------------------------

display ::
  forall j t m. (MonadState [String] m, VarLike j, SyntaxWithBinding t)
         => Alg j t (CONST String) (Compose m (CONST String))
         => forall a. (j a -> String) -> Syntax j t a -> m String
display rho = fmap runCONST . runCompose . eval' (Proxy :: Proxy (CONST String)) (CONST . rho)

display' ::
  forall t. SyntaxWithBinding t
         => Alg Fin t (CONST String) (Compose (State [String]) (CONST String))
         => Syntax Fin t 'Zero -> String
display' = flip evalState names . display finZero

  where

    alpha = ['a'..'z']
    names = fmap (:[]) alpha
          ++ zipWith (\ c -> (c:) . show) (cycle alpha) [(1 :: Integer)..]


