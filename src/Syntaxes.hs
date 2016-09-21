{-# OPTIONS -Wall                  #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DeriveAnyClass        #-}

module Syntaxes where

import Data.Function
import Data.Proxy
import Data.Functor.Classes
import Control.Newtype
import Control.Monad.Reader
import Control.Monad.State

import Utils
import Scopes
import Generic

-------------------------------------------------------------
-- UNTYPED LAMBDA CALCULUS
-------------------------------------------------------------

type Term = Syntax Variable TmF

data TmF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  L :: s (r s) a      -> TmF r s a -- Lambda Abstraction
  A :: r s a -> r s a -> TmF r s a -- Application

instance SyntaxWithBinding TmF where
  reindex r s e = case e of
    L b   -> L $ s b
    A f t -> A (r f) (r t)
instance Functor Term where fmap = hfmap . over Variable

instance (Eq1 (r s), Eq1 (s (r s))) => Eq1 (TmF r s) where
  L b   `eq1` L b'    = b `eq1` b'
  A f t `eq1` A f' t' = f `eq1` f' && t `eq1` t'
  _     `eq1` _       = False

instance (Eq1 (r s), Eq1 (s (r s)), Eq a) => Eq (TmF r s a) where
  (==) = eq1

pattern TmL t   = Fix (L t)
pattern TmA f t = Fix (A f t)

pattern TmL' t   = Fix (L (Scope t))

-------------------------------------------------------------
-- MINI TT
-------------------------------------------------------------


type TT = Syntax Fin TTF

data TTF (r :: ((Natural -> *) -> (Natural -> *)) -> (Natural -> *))
         (s :: (Natural -> *) -> (Natural -> *))
         (a :: Natural)
         :: * where
  PI   :: r s a -> s (r s) a -> TTF r s a
  LM   :: s (r s) a -> TTF r s a
  (:$) :: r s a -> r s a -> TTF r s a

instance SyntaxWithBinding TTF where
  reindex r s e = case e of
    PI a b -> PI (r a) $ s b
    LM b   -> LM $ s b
    f :$ t -> ((:$) `on` r) f t

pattern TTPI a b = Fix (PI a b)
pattern TTLM b   = Fix (LM b)
pattern TTAP f t = Fix (f :$ t)

-------------------------------------------------------------
-- CYCLIC LISTS
-------------------------------------------------------------

data CLF (e :: *) -- element type
         (r :: ((Natural -> *) -> (Natural -> *)) -> (Natural -> *))
         (s :: (Natural -> *) -> (Natural -> *))
         (a :: Natural)
         :: * where
  NIL  :: CLF e r s a
  (:<) :: e -> s (r s) a -> CLF e r s a

type CL e = Fix Fin (CLF e) (Scope Fin)

instance SyntaxWithBinding (CLF e) where
  reindex _ s e = case e of
    NIL      -> NIL
    hd :< tl -> hd :< s tl

pattern CLNIL       = Fix NIL
pattern CLCON  e es = Fix (e :< es)
pattern CLCON' e es = CLCON e (Scope es)

instance Alg Fin (CLF e) (CONST [e]) (CONST [e]) where
  ret _ _ = id
  alg _ e = case e of
    NIL      -> CONST []
    hd :< tl -> let prfx :: CONST [e] ~> CONST [e]
                    prfx = over CONST (hd :)
                in prfx $ fixpoint' prfx $ kripke runConst tl

toStream :: forall e. CList e -> [e]
  -- contracting this type signature using ~> takes `e` out
  -- of scope which makes it impossible to mention it in the
  -- proxy type in the body of the function!
toStream = runCONST . eval' (Proxy :: Proxy (CONST [e])) finZero . runCList

instance MonadReader (e -> f) m => Alg Fin (CLF e) Fin (Compose m (CL f)) where
  ret _ _ = Compose . return . Var
  alg _ e = Compose $ case e of
    NIL      -> return CLNIL
    hd :< tl ->
      let hd' = fmap ($ hd) ask
          tl' = fmap Scope $ runCompose $ runScope $ abstract' id tl
      in CLCON <$> hd' <*> tl'

newtype CList a = CList { runCList :: CL a 'Zero }

instance Newtype (CList a) (CL a 'Zero) where
  pack = CList
  unpack = runCList

instance Functor CList where
  fmap f = over CList $ ($ f) . runCompose . eval' (Proxy :: Proxy Fin) finZero

-------------------------------------------------------------
-- NESTED SCOPES
-------------------------------------------------------------

type YTM = Syntax Fin YF

data YF s r a :: * where
  YA :: r s a -> r s a -> YF r s a
  Y1 :: s (r s) a -> YF r s a
  Y2 :: s (r s) a -> YF r s a

pattern Y f = Fix (Y2 (Scope (Fix (Y1 (Scope f)))))

instance SyntaxWithBinding YF where
  reindex r s e = case e of
    YA f t -> YA (r f) (r t)
    Y1 f   -> Y1 $ s f
    Y2 f   -> Y2 $ s f

instance MonadState [String]  m => Alg Fin YF (CONST String) (Compose m (CONST String)) where
  ret _ _ = Compose . return
  alg _ e = Compose $ case e of
    YA f t -> do
      fstr <- runCONST <$> (runCompose $ runConst f)
      tstr <- runCONST <$> (runCompose $ runConst t)
      return $ CONST $ concat [ "YA (", fstr, ") (", tstr, ")" ]
    Y2 f -> do
      (hd : tl) <- get
      put tl
      fstr <- runCONST <$> (runCompose $ runConst $ runKripke f id (CONST hd))
      return $ CONST $ concat [ "mu ", hd, ". ", fstr ]
    Y1 f -> do
      (hd : tl) <- get
      put tl
      fstr <- runCONST <$> (runCompose $ runConst $ runKripke f id (CONST hd))
      return $ CONST $ concat [ "lam ", hd, ". ", fstr ]

-------------------------------------------------------------
-- ALGEBRAS FOR NORMALISATION BY EVALUATION
-------------------------------------------------------------

instance Alg Variable TmF (Model Variable TmF) (Model Variable TmF) where
  ret _ _ = id
  alg _ e = case e of
    L b   -> Model $ Fix $ L $ kripke (runModel . runConst) b
    A f t -> case runModel (runConst t) of
      Fix (L b) -> Model $ runKripke b id (runConst t)
      _         -> Model $ Fix $ (A `on` runModel . runConst) f t

instance Alg Fin YF (Model Fin YF) (Model Fin YF) where
  ret _ _ = id
  alg _ e = Model $ case e of
    YA f t -> case runModel (runConst f) of
      (Fix (Y2 g)) -> case runModel (fixpoint $ kripke Model g) of
        Fix (Y1 h) -> runKripke h id (runConst t)
        _          -> error "IMPOSSIBLE: Y2 always preceded by Y1"
      _    -> Fix $ (YA `on` runModel . runConst) f t
    Y1 f   -> Fix $ Y1 $ kripke (runModel . runConst) f
    Y2 f   -> Fix $ Y2 $ kripke (runModel . runConst) f

-------------------------------------------------------------
-- SHOW INSTANCES
-------------------------------------------------------------

instance (Show1 (r s), Show1 (s (r s))) => Show1 (TmF r s) where
  showsPrec1 i e = case e of
    L b   -> showString "L " . showsPrec1 (1+i) b
    A f t -> showsBinary1 "A" i f t

deriving instance (Show (r s a), Show (s (r s) a)) => Show (TmF r s a)


instance (MonadState [String] m, Show e) => Alg Fin (CLF e) (CONST String) (Compose m (CONST String)) where
  ret _ _ = Compose . return
  alg _ e = Compose $ case e of
    NIL      -> return $ CONST "NIL"
    hd :< tl -> do
      (nm : rest) <- get
      put rest
      str <- runCompose $ runScope $ abstract' (const $ CONST nm) tl
      return $ over CONST ((concat ["fix ", nm, ". ", show hd, " :< "]) ++) str

-- Trick to avoid the overlapping instance with `Fix ...` declared
-- generically a bit earlier
instance Show e => Show (Apply (CL e) n) where
  show e = case runApply e of
    Var a       -> "Var " ++ show a
    CLNIL       -> "NIL"
    CLCON hd tl -> show hd ++ " :< " ++ show (Apply $ runScope tl)

instance Show e => Show (CList e) where
  show = show . Apply . runCList

