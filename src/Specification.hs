{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Specification where


import Utils
import Scopes
import Generic
import Syntaxes

spec_VarLike :: (VarLike j, Eq (j (Next j a))) => j (Next j a) -> Bool
spec_VarLike v = inspect var0 weak v == v

spec_SyntaxWithBindingId :: (SyntaxWithBinding t, Eq (t r s a)) => t r s a -> Bool
spec_SyntaxWithBindingId t = reindex id id t == t

spec_SyntaxWithBindingCompose ::
    forall r r' r''
           (s   :: (i -> *) -> (i -> *))
           (s'  :: (i -> *) -> (i -> *))
           (s'' :: (i -> *) -> (i -> *))
           t a b c.
    (SyntaxWithBinding t, Eq (t r'' s'' c)) =>
    (r  s  a -> r'  s'  b) -> (s  (r  s)  a -> s'  (r'  s')  b) ->
    (r' s' b -> r'' s'' c) -> (s' (r' s') b -> s'' (r'' s'') c) -> 
    (t r s a) -> Bool
spec_SyntaxWithBindingCompose r1 s1 r2 s2 t =
  reindex r2 s2 (reindex r1 s1 t)
  == reindex (r2 . r1) (s2 . s1) t

{-# RULES
"inspect/var0weak" inspect var0 weak = id
"reindex/id"       reindex id id = id
"reindex/reindex"  forall r1 s1 r2 s2. reindex r2 s2 . reindex r1 s1 = reindex (r2 . r1) (s2 . s1)
 #-}

