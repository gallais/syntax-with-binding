%-----------------------------------------------------------------------------
%
%               Template for sigplanconf LaTeX Class
%
% Name:         sigplanconf-template.tex
%
% Purpose:      A template for sigplanconf.cls, which is a LaTeX 2e class
%               file for SIGPLAN conference proceedings.
%
% Guide:        Refer to "Author's Guide to the ACM SIGPLAN Class,"
%               sigplanconf-guide.pdf
%
% Author:       Paul C. Anagnostopoulos
%               Windfall Software
%               978 371-2316
%               paul@windfall.com
%
% Created:      15 February 2005
%
%-----------------------------------------------------------------------------


\documentclass[preprint]{sigplanconf}

% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% numbers       To obtain numeric citation style instead of author/year.

\usepackage{amsmath}
\usepackage{todonotes}
\usepackage{mathpartir}
%include lhs2TeX.fmt
%include forall.fmt
\newcommand{\cL}{{\cal L}}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{PEPM '17}{January 16--17, 2017, Paris, France}
\copyrightyear{2016}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

\titlebanner{DRAFT}        % These are ignored unless
%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{A Generic Treatment of Syntaxes with Binding in Haskell}
% \subtitle{Subtitle Text, if any}

\authorinfo{Allais Guillaume}
           {Radboud University, Nijmegen}
           {gallais@@cs.ru.nl}


%format kind = "\mathbf{kind}"

\maketitle

\begin{abstract}
\end{abstract}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
\terms
term1, term2

\keywords
keyword1, keyword2

\section{Introduction}

The software programmer developping an embedded DSL and the PL
researcher formalising a calculus face similar challenges: they
both need to (re)implement common traversals such as renaming,
subtitution, or an evaluation procedure.

\todo{LAWS!!!}
\begin{hide}

> {-# LANGUAGE RankNTypes     #-}
> {-# LANGUAGE DeriveFunctor  #-}
> {-# LANGUAGE PolyKinds      #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE TypeOperators  #-}
> import Data.Function
> import Data.Tuple

\end{hide}

> data T a = V a | A (T a) (T a) | L (T (Maybe a))
>
> rename :: (a -> b) -> (T a -> T b)
> rename rho e = case e of
>   V a    -> V (rho a)
>   A f t  -> (A `on` rename rho) f t
>   L b    -> L (rename (extend rho) b)
>   where extend = maybe Nothing . (Just .)
>
> subst :: (a -> T b) -> (T a -> T b)
> subst rho e = case e of
>   V a    -> rho a
>   A f t  -> (A `on` subst rho) f t
>   L b    -> L (subst (extend rho) b)
>   where extend = maybe (V Nothing) . (rename Just .)

Looking at these two functions, it is quite evident that they have
a very similar format. Making this shared structure explicit would
allow for these definitions to be refactored, and their properties
to be proved in one swift move.

\subsection{Refactoring Renaming and Substitution using $\mathit{Kit}$s}

Previous efforts in dependently-typed programming~\cite{mcbride2005type,benton2012strongly}
have made it possible to refactor renaming and substitution as two
instances of a more general traversal. For a given calculus $\mathcal{T}$,
an abstract set of constraints $\mathit{Kit}(\mathcal{E})$ characterises
the conditions under which one can define this generalisation:
$$|kit :: Kit|(\mathcal{E}) |->| (a |->| \mathcal{E}(b))
                            |->| (\mathcal{T}(a) |->| \mathcal{T}(b))$$
Benton et al. in particular showed that this refactoring strategy can be
applied not only to the language used by McBride in his original draft but
also to other $\lambda{}$-calculi such as System F~\cite{reynolds1983types}.
However this generic presentation was still limited to renaming and substitution
when other semantics did present a resembling shape:

> data Val = LM (Val -> Val)
> 
> eval :: (a -> Val) -> (T a -> Val)
> eval rho e = case e of
>   V a    -> rho a
>   A f t  -> (app `on` eval rho) f t
>   L b    -> LM (\ v -> eval (maybe v rho) b)
>   where app (LM f) t = f t

\subsection{Capturing Other Semantics Too using $\mathit{Model}$s}

Lately this approach has been extended to a wealth of other semantics
from various variations on normalisation by evaluation to printing
with names or CPS transformations~\cite{allais2016type}. Allais, Chapman,
and McBride defined a simply-typed $\lambda{}$-calculus $\mathcal{T}$ and
spelt out the set of constraints $\mathit{Model}(\mathcal{E}, \mathcal{V})$
two predicates $\mathcal{E}$ and $\mathcal{V}$ have to satisfy for the
more general evaluation function $\mathit{model}$ to be definable:
$$|model :: Model|(\mathcal{E}, \mathcal{V}) |->| (a |->| \mathcal{E} b)
                                             |->| (\mathcal{T} a |->| \mathcal{V} b)$$
This made it possible to refactor a lot of semantics through $\mathit{model}$
but, perhaps more importantly, it also made it possible to prove some of their
properties generically. Indeed, they provide an abstract characterisation of
$\mathit{Model}$s for which one can prove the fundamental theorem of logical
relations for the corresponding instanciation of $\mathit{model}$\todo{explain related inputs to related outputs?}, as well as
an abstract framework to prove fusion laws.

\subsection{Towards a Generic Treatment of Syntaxes with Binding}

All these formalisations have been focusing on one language at a
time, showcasing various techniques making it possible to study its
properties in a principled manner. However the construction of the
$\mathit{Model}$ constraint is quite evidently directed by the shape
of the language being studied. This paper sets out to show that it
is indeed the case by demonstrating that one can describe generically
the constructions which were until now ad-hoc.

Section~\ref{knot} recalls a useful approach to generic programming
in Haskell colloquially known as ``Tying the Knot'' (at the type
level in this case). This design principle guides the definition of
what an abstract notion of syntax with binding landing itself to a
generic treatment ought to be.

Section~\ref{scopesem} describes uniformly for all syntaxes with
binding the analogue of the $\mathit{Model}$ constraint that two
predicates have to satisfy for the corresponding semantics to be
factored through the generic evaluation function. A constraint on
what constitutes a valid syntax with binding is also derived from
the properties required to prove that the evaluation function
indeed exists.

\todo{plan}

\section{(Un)Tying the Knot}
\label{knot}
\cite{swierstra2008data}
\todo{caveats: inductive fragment, total functions}

\subsection{Datatypes as Fixpoints of Functors}

> data Partial e a = Error e | Result a
> partial :: (e -> b) -> (a -> b) -> Partial e a -> b
> partial error result p = case p of
>   Error e  -> error e
>   Result a -> result a
> results :: Partial e a -> [a]
> results = partial (const []) pure
>
> data BTree a = Leaf a | Node (BTree a) (BTree a)
> btree :: (a -> b) -> (b -> b -> b) -> BTree a -> b
> btree leaf node t = case t of
>   Leaf a    -> leaf a
>   Node l r  -> (node `on` btree leaf node) l r
> 
> leafs :: BTree a -> [a]
> leafs = btree pure (++)

> data Knot f = Knot (f (Knot f))
> knot :: Functor f => (f r -> r) -> Knot f -> r
> knot alg (Knot t) = alg $ fmap (knot alg) t

> data PartialF e a r = ErrorF e | ResultF a
>   deriving Functor
> type Partial' e a = Knot (PartialF e a)
> 
> partial' :: (e -> b) -> (a -> b) -> Partial' e a -> b
> partial' error result = knot $ \ p -> case p of
>   ErrorF e   -> error e
>   ResultF r  -> result r
>
> data BTreeF a r = LeafF a | NodeF r r
>   deriving Functor
> type BTree' a = Knot (BTreeF a)
>
> btree' :: (a -> b) -> (b -> b -> b) -> BTree' a -> b
> btree' leaf node = knot $ \ t -> case t of
>   LeafF a    -> leaf a
>   NodeF l r  -> node l r

\subsection{Non-Regular Datatypes and the Functor Category}

> data CBTree a = CLeaf a | CNode (CBTree (a, a))
>   deriving Show
> cbtree  :: (forall a. a -> b a) ->  (forall a. b (a, a) -> b a)
>         -> CBTree a -> b a
> cbtree cleaf cnode t = case t of
>   CLeaf a -> cleaf a
>   CNode n -> cnode (cbtree cleaf cnode n)
>
> cleafs :: CBTree a -> [a]
> cleafs = cbtree pure $ concatMap $ \(l,r) -> [l,r]

%format ~> = "\rightsquigarrow"

In the functor category, natural transformations are the appropriate
notion of morphism between two functors. We introduce a type operator
|(~>)| to denote those and define the |HFunctor| class (for ``Higher
Functor'') to represent functors between functors. \todo{discuss kinds, *}

> type (~>) s t = forall a. s a -> t a
>
> class HFunctor (f :: (i -> *) -> (i -> *)) where
>   hfmap :: (s ~> t) -> (f s ~> f t)

One can, again, define the fixpoint of these higher functors
and they too come with an appropriate notion of fold: it turns
an algebra (a natural transformation |f b ~> b|) into an
iterator (a natural transformation |HKnot f ~> b|).

> data HKnot f a = HKnot (f (HKnot f) a)
> hknot :: HFunctor f => (f b ~> b) -> HKnot f ~> b
> hknot alg (HKnot t) = alg $ hfmap (hknot alg) t
>
> data CBTreeF r a = CLeafF a | CNodeF (r (a, a))
> type CBTree' a = HKnot CBTreeF a
> instance HFunctor CBTreeF where
>   hfmap f t = case t of
>     CLeafF a  -> CLeafF a
>     CNodeF n  -> CNodeF $ f n
> 
> cbtree'  :: (forall a. a -> b a) -> (forall a. b (a, a) -> b a)
>          -> CBTree' ~> b
> cbtree' leaf node = hknot $ \ t -> case t of
>   CLeafF a  -> leaf a
>   CNodeF n  -> node n


We have seen that describing recursive types as the fixpoints
of endofunctors makes it possible to provide generic functions
manipulating them. Depending which category these endofunctors
are based on, the expressive power varies: Set is good enough
for the most basic inductive types whilst more complex ones
(such as non-regular datatypes) are captured by more complex
categories (such as the functor one).

\section{Syntaxes with Binding as Fixpoints}

The fundamental structure of a syntax with binding is not only
given by a notion of recursive positions serving as placeholders
for subterms but also a notion of scope-transformations which
are invoked when describing a binder: they take the current
scope and extend it with a fresh variable.

To make this structure explicit we introduce the following
|kind| synonyms. This is not valid Haskell code\footnote{The
@TypeInType@ ghc language extension does allow to define
something similar by merging the notions of type and kind.}
but it will hopefully help the reader by breaking down an
otherwise enormous kind signature into smaller, understandable
chunks.

> kind Scoped   i = i -> *

A |Scoped i| type is a type indexed by a kind |i| which represents
the scope of the variables it may refer to. Through the litterature
we mainly find three different kind used for |i|.

First of all, |*| itself is used in Altenkirch and Reus' seminal
paper~\cite{altenkirch1999monadic}. Variables are inhabitants of
the index type which means that the empty type can be used to
guarantee that a term is closed and that the |Maybe| type constructor
is the right notion of scope-extension: |Maybe a| has exactly one
more inhabitant than |a|.

Secondly, given that |*| is typically used in a finitary manner
(every term is notionally indexed by |Maybe^n Void| for some n,
one can make this explicit by using |Nat| instead. Variables in
an |n|-term then correspond to inhabitants of the |Fin n| family,
an inductive family~\cite{dybjer1991inductive} which has exactly
|n| inhabitants.

Finally, well-typed approaches may use a notion of scope with
more structure. To represent the simply-typed lambda calculus,
one will typically use |[Type]| where |Type| is a datatype
describing the simple types this language uses. Variables are
positions in such a list, the empty list is used for closed terms
and consing a |Type| on top of an existing list gives the appropriate
notion of scope-extension a binder requires.

> kind ScopedT  i = Scoped i -> Scoped i
> newtype Body t a = Body { runBody :: t (Maybe a) }

A scoped-transformer |ScopedT i| is a function turning a
|Scoped i| type into another one. A typical example of a
|ScopedT *| is the |Body| type.

> kind Syntax   i = ScopedT i -> Scoped i
> kind SyntaxT  i = Syntax i -> Syntax i

> class SyntaxWithBinding (t :: SyntaxT i) where
>   reindex  ::  (r s a -> v w b)
>            ->  (s (r s) a -> w (v w) b)
>            ->  (t r s a -> t v w b)

\paragraph{Untyped Lambda Calculus}

\paragraph{PCF}

\paragraph{Cyclic Lists}

\section{Scope Preserving Semantics}
\label{scopesem}
\cite{allais2016type}

\section{Syntaxes and their Fundamental Lemma}

\subsection{Renaming and Substitution}

\subsection{Normalisation by Evaluation}

\subsection{Printing with Names}

\subsection{Other Traversals}

\paragraph{Cyclic lists as functors}
\paragraph{Unfolding cyclic lists to streams}


\section{Syntax and Relative Monads}
\cite{altenkirch2014relative}

\section{Limitations and Future Work}

Not all interesting traversals can be obtained as one of our
evaluation functions. A prime example of this is the definition
of normalisation obtained by reducing terms using a big step
semantics as showcased in~\cite{abel2014normalization}. Indeed,
when evaluating an application (Figure~\ref{bsapp}), it is not
enough to combine the results obtained by recursively applying
the algorithm to the function and its argument: one may still
need to restart the computation if the function has normalised
to a lambda abstraction! These type of traversals are quite
simply out of scope here.

\begin{figure}
\begin{mathpar}
\inferrule
 {   t \Downarrow{} \lambda{}x. b
\and u \Downarrow{} a
\and b [a /x] \Downarrow{} v
}{   t(u) \Downarrow{} v
}    
\end{mathpar}
\caption{Big step semantics: the application case\label{bsapp}}
\end{figure}


The current definition of the @SyntaxWithBinding@ class is quite
restrictive. This is both a blessing which makes the fundamental
lemma of syntaxes provable but also a curse limiting the user's
ability to express whatever she wants. For instance, it is not
possible to nest multiple uses of the scope transformer when
defining a syntax. In other words, she will not be able to implement
@reindex@ for a simple language comprising application and recursive
functions which could be described using the following datatype:

> data  YF r s a =
>      AP (r s a) (r s a)
>   |  Y (s (s (r s)) a)

where the intended meaning of @Y@ is

> y :: ((a -> b) -> (a -> b)) -> (a -> b)
> y f x = f (y f) x

The situation is however somewhat salvageable: @Y@ can
be decomposed into @Y1@ and @Y2@ both using only one
scope transformer and @Y@ recovered for the fixpoint of @YF'@
by using a pattern synonym composing @Y1@ and @Y2@.

> data  YF' r s a =
>      AP' (r s a) (r s a)
>   |  Y1' (s (r s) a)
>   |  Y2' (s (r s) a)

Writing semantics for this language however becomes quite annoying:
either @Y1@ and @Y2@ have to be handled separately (which can be
done when defining Normalisation by Evaluation for instance) or the
model has to be polluted with extra information making it possible
to retain information contained in @Y1@ so that it is made available
when handling @Y2@.

\todo{categorical structure}
\todo{MiniAgda}

The work mentioned in section~\ref{scopesem} and presented in the
draft~\cite{allais2016type} is not limited to refactoring usual
semantics through a common abstract notion of model. It also provides
a framework to prove generically these semantics' properties. Once
again, the structure of the framework is tightly connected to the
structure of the studied language. It is a rather natural endeavour
to extend these proof frameworks to the generic case. Because of the
typed, strongly normalising setting, the proofs in~\cite{allais2016type}
are constructed using logical relations\todo{cite}. However the
extension of these proof techniques to any syntax with binding will
have to do away with such strong guarantees: normalisation by evaluation
for the untyped lambda calculus may very well not terminate! The more
refined notion of step-indexed logical relations \todo{cite}\todo{finite unfolding}
is an ideal candidate.



% We recommend abbrvnat bibliography style.
\bibliographystyle{abbrvnat}
\bibliography{main}

% The bibliography should be embedded for final submission.
%\begin{thebibliography}{}
%\softraggedright
%\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%P. Q. Smith, and X. Y. Jones. ...reference text...
%\end{thebibliography}


\end{document}
