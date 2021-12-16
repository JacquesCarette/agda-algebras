This is ``Jacques' version'' of HSP. It was started from \texttt{HSP.laga} (as it was when
submitted to the TYPES post-proceedings). The changes are largely stylistic.

\section{Introduction}
The \agdaalgebras library \cite{ualib_v2.0.1} formalizes the foundations of universal algebra
in intensional Martin-Löf type theory (\mltt) using \agda~{Norell:2007,agdaref}.
It aims to codify the basics ofclassical set-theory-based universal algebra and equational
logic.

The first major milestone is a proof of \emph{Birkhoff's
variety theorem} (also known as the \emph{HSP theorem})~\cite{Birkhoff:1935}.
To the best of our knowledge, this is the first machine-verified proof of Birkoff's
celebrated 1935 result.

What follows is a self-contained proof of the HSP theorem, written as a literate
\agda file\footnote{compatible with\agda ver.2.6.2 and \agdastdlib ver.1.7
and available at\url{https://github.com/ualib/agda-algebras/blob/master/src/Demos/HSP.lagda}}
.

%In the course of this presentation we highlight some of the challenging aspects of
%formalizing the basic definitions and theorems of universal algebra in type theory.

\section{Preliminaries}

\subsection{Logical foundations}

We set the options to makge \agda behave as closely to \mltt as possible.
\begin{code}[inline]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}
.
\AgdaPragma{without-K} disables
\href{https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29}{Streicher's K axiom},
\AgdaPragma{exact-split} directs \agda to accept only definitions behaving like
{\it judgmental} equalities, and
\AgdaPragma{safe} ensures that nothing is postulated outright.
See~\cite{agdaref-axiomk,agdaref-safeagda,agdatools-patternmatching} for more details.

\begin{code}


module Demos.HSP-J where
-- Import 16 definitions from the Agda Standard Library.
open import  Data.Unit.Polymorphic                           using ( ⊤ ; tt                        )
open import  Function                                        using ( id ; flip ; _∘_               )
open import  Level                                           using ( Level                         )
open import  Relation.Binary                                 using ( Rel ; Setoid ; IsEquivalence  )
open import  Relation.Binary.Definitions                     using ( Reflexive ; Symmetric         )
                                                             using ( Transitive ; Sym ; Trans      )
open import  Relation.Binary.PropositionalEquality           using ( _≡_                           )
open import  Relation.Unary                                  using ( Pred ; _⊆_ ; _∈_              )

-- Import 23 definitions from the Agda Standard Library and rename 12 of them.
open import  Agda.Primitive  renaming ( Set    to Type    )  using ( _⊔_ ; lsuc                    )
open import  Data.Product    renaming ( proj₁  to fst     )
                             renaming ( proj₂  to snd     )  using ( _×_ ; _,_ ; Σ ; Σ-syntax      )
open import  Function        renaming ( Func   to _⟶_     )  using ( IsInjection ; Surjection        )
import  Function.Construct.Identity as FId
import  Function.Construct.Composition as FComp
open         _⟶_             renaming ( f      to _⟨$⟩_   )  using ( cong                          )
open         Setoid          renaming ( refl   to reflˢ   )
                             renaming ( sym    to symˢ    )
                             renaming ( trans  to transˢ  )
                             renaming ( _≈_    to _≈ˢ_    )  using ( Carrier ; isEquivalence       )
open         IsEquivalence   renaming ( refl   to reflᵉ   )
                             renaming ( sym    to symᵉ    )
                             renaming ( trans  to transᵉ  )  using ()
\end{code}
\ifshort\else
\begin{code}
-- Assign handles to 3 modules of the Agda Standard Library.
import       Function.Definitions                   as FD
import       Relation.Binary.PropositionalEquality  as ≡
import       Relation.Binary.Reasoning.Setoid       as SetoidReasoning

record Signature (𝓞 𝓥 : Level) : Type (lsuc (𝓞 ⊔ 𝓥)) where
  constructor sig
  field
    ops : Type 𝓞
    arity : ops → Type 𝓥

open Signature

private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ ℓ′ 𝓞 𝓥 : Level
 Γ Δ : Type χ

\end{code}
\fi
Note that the above imports include some adjustments to ``standard \agda'' syntax to suit our own taste.
In particular, the following conventions used throughout the \agdaalgebras library and this paper:
we use \AgdaPrimitive{Type} in place of \AgdaPrimitive{Set}, the infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, instead of
\AgdaRecord{Func} (the type of ``setoid functions'' discussed in §\ref{setoid-functions} below),
and the symbol \aofld{\au{}⟨\$⟩\au{}} in place of \afld{f} (application of the map of a setoid function); we use
\AgdaField{fst} and \AgdaField{snd}, and sometimes \AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}} and
\AgdaOperator{\AgdaFunction{∥\AgdaUnderscore{}∥}}, to denote the first and second
projections out of the product type
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}×\AgdaUnderscore{}}}.
\ifshort\else

\begin{code}

module _ {A : Type α }{B : A → Type β} where
 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst
 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
\end{code}
\fi

%% -----------------------------------------------------------------------------
\subsection{Setoids}\label{setoids}

Constructively, setoids which pair a carrier with its own equivalence relation,
work much better than sets and a ``global'' equivalence. Luckily, \agda's
standard library comes well equipped to deal with these.

Some of them are a bit inconvenient, so we create some synonyms that take more
arguments implicitly.

\begin{code}

𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A = A} = FId.function A

_⟨∘⟩_ :  {A : Setoid α ρᵃ} {B : Setoid β ρᵇ} {C : Setoid γ ρᶜ}
 →       B ⟶ C  →  A ⟶ B  →  A ⟶ C
f ⟨∘⟩ g = FComp.function g f
\end{code}

\paragraph*{Injective and surjective setoid functions}
If \ab{f} % : \ab{𝑨} \aor{⟶} \ab{𝑩}
is a setoid function from % \ab{𝑨} =
(\ab A, \af{≈ᴬ}) to
% \ab{𝑩} =
(\ab B, \af{≈ᴮ}), then we call \ab f \defn{injective} provided
\as{∀} (\ab{a₀} \ab{a₁} \as : \ab{A}), \ab{f} \aofld{⟨\$⟩} \ab{a₀} \af{≈ᴮ} \ab{f} \aofld{⟨\$⟩} \ab{a₁}
implies \ab{a₀} \af{≈ᴬ} \ab{a₁}; we call \ab{f} \defn{surjective} provided
\as{∀} (\AgdaTyped{b}{B}), \as{∃}~(\AgdaTyped{a}{A}) such that \ab{f} \aofld{⟨\$⟩} \ab{a} \af{≈ᴮ} \ab{b}.
The \agdastdlib represents injective functions on bare types by the
type \af{Injective}, and uses this to define the \af{IsInjective} type to represent
the property of being an injective setoid function. Similarly, the type \af{IsSurjective}
represents the property of being a surjective setoid function. \af{SurjInv} represents the \emph{right-inverse} of a surjective function.
\ifshort %%% BEGIN SHORT VERSION ONLY
 We omit the straightforward definitions and proofs of these types, but \seeshort for details.
\else    %%% END SHORT VERSION ONLY
         %%% BEGIN LONG VERSION ONLY SECTION
 We reproduce the definitions and prove some of their properties
 inside the next submodule where we first set the stage by declaring two
 setoids \ab{𝑨} and \ab{𝑩}, naming their equality relations, and making some
 definitions from the standard library available.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑨 using () renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝑩 using () renaming ( _≈_ to _≈ᴮ_ )
 open FD _≈ᴬ_ _≈ᴮ_

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective (_⟨$⟩_ f)

 IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
 IsSurjective f = Surjective (_⟨$⟩_ f)

 SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → Carrier 𝑩 → Carrier 𝑨
 SurjInv f fonto b = fst (fonto b)

\end{code}

Proving that the composition of injective setoid functions is again injective
is simply a matter of composing the two assumed witnesses to injectivity.
Proving that surjectivity is preserved under composition is only slightly more involved.

\begin{code}

module _  {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ}
          (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪) where

 ∘-IsInjective : IsInjective f → IsInjective g → IsInjective (g ⟨∘⟩ f)
 ∘-IsInjective finj ginj = finj ∘ ginj

 ∘-IsSurjective : IsSurjective f → IsSurjective g → IsSurjective (g ⟨∘⟩ f)
 ∘-IsSurjective = FComp.surjective (Setoid._≈_ 𝑨) (Setoid._≈_ 𝑩) (Setoid._≈_ 𝑪) (Setoid.trans 𝑪) (cong g)
\end{code}
\fi      %%% END LONG VERSION ONLY SECTION

\paragraph*{Kernels of setoid functions}
The \defn{kernel} of a function \ab f~\as :~\ab A~\as{→}~\ab B (where \ab A and \ab B are bare types) is defined
informally by \{\AgdaPair{x}{y} \aod{∈} \ab A \aof{×} \ab A \as : \ab f \ab x \as{=} \ab f \ab y \}.
This can be represented in \agda in a number of ways, but for our purposes it is most
convenient to define the kernel as an inhabitant of a (unary) predicate over the square of
the function's domain, as follows.

The kernel of a \emph{setoid} function \ab f \as : \ab{𝐴} \aor{⟶} \ab{𝐵} is
\{\AgdaPair{x}{y} \as{∈} \ab A \aof{×} \ab A \as : \ab f \aofld{⟨\$⟩} \ab x \af{≈} \ab f \aofld{⟨\$⟩} \ab y\},
where \af{\au{}≈\au} denotes equality in \ab{𝐵}. This can be formalized in \agda as follows.

\begin{code}

module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
 open Setoid 𝐴 using () renaming ( Carrier to A )

 ker : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
 ker g (x , y) = g ⟨$⟩ x ≈ g ⟨$⟩ y where open Setoid 𝐵 using ( _≈_ )
\end{code}


%% -------------------------------------------------------------------------------------

\section{Types for Basic Universal Algebra}
\label{types-for-basic-universal-algebra}
In this section we develop a working vocabulary and formal types for classical,
single-sorted, set-based universal algebra.
We cover a number of important concepts, but we limit ourselves to those
concepts required in our formal proof of Birkhoff's HSP theorem.
In each case, we give a type-theoretic version of the informal definition,
followed by a formal implementation of the definition in \mltt using the \agda language.

\ifshort\else
This section is organized into the following subsections:
§\ref{signatures} defines a general notion of \emph{signature} of a structure and then defines a type that represent signatures;
§\ref{algebras} does the same for \emph{algebraic structures} and \emph{product algebras};
§\ref{homomorphisms} defines \emph{homomorphisms}, \emph{monomorphisms}, and \emph{epimorphisms}, presents types that codify these concepts and formally verifies some of their basic properties;
§§\ref{subalgebras}--\ref{terms} do the same for \emph{subalgebras} and \emph{terms}, respectively.
\fi

%% -----------------------------------------------------------------------------
\subsection{Signatures}
\label{signatures}

\ifshort
An (algebraic) \defn{signature}
\else
In model theory, the \defn{signature} of a structure is a quadruple \ab{𝑆} = (\ab{C},
\ab{F}, \ab{R}, \ab{ρ}) consisting of three (possibly empty) sets \ab{C}, \ab{F}, and
\ab{R}---called \emph{constant}, \emph{function}, and \emph{relation} symbols,
respectively---along with a function \ab{ρ} : \ab{C} \as{+} \ab{F} \as{+} \ab{R}
\as{→} \ab{N} that assigns an \emph{arity} to each symbol. Often, but not always, \ab{N}
is taken to be the set of natural numbers.

As our focus here is universal algebra, we consider the restricted notion of an
\emph{algebraic signature}, that is, a signature for ``purely algebraic'' structures. Such
a signature
\fi
is a pair \ab{𝑆} = \AgdaPair{F}{ρ} where \ab{F} is a collection of
\defn{operation symbols} and \ab{ρ} : \ab{F} \as{→} \ab{N} is an \defn{arity function}
which maps each operation symbol to its arity. Here, \ab{N} denotes the \emph{arity type}.
Heuristically, the arity \ab{ρ} \ab{f} of an operation symbol \ab{f} \as{∈} \ab{F} may be
thought of as the number of arguments that \ab{f} takes as ``input.''

The \agdaalgebras library represents an algebraic signature as an
inhabitant of the following dependent pair type:

\begin{center}

\AgdaFunction{Signature}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPostulate{Level}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaPrimitive{Type}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaPrimitive{lsuc}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaOperator{\AgdaPrimitive{⊔}}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSymbol{))}\\[4pt]
\AgdaFunction{Signature}\AgdaSpace{}%
\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{Σ[}\AgdaSpace{}%
\AgdaBound{F}\AgdaSpace{}%
\AgdaFunction{∈}\AgdaSpace{}%
\AgdaPrimitive{Type}\AgdaSpace{}%
\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaFunction{]}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{F}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaPrimitive{Type}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSymbol{)}

\end{center}

We need to augment the ordinary \af{Signature} type so that it supports algebras over
setoid domains.
\ifshort\else
To do so---following Andreas Abel's lead (cf.~\cite{Abel:2021})---we
define an operator that translates an ordinary signature into a \defn{setoid signature},
that is, a signature over a setoid domain.
\fi
This raises a minor technical issue concerning
the dependent types involved in the definition.
\ifshort\else
Some readers might find the resolution of
this issue instructive, so let's discuss it briefly.
\fi
If we are given two operations \ab{f} and \ab{g}, a tuple \ab{u} \as{:} \aof{∥} \ab{𝑆} \aof{∥} \ab{f} \as{→}
\ab{A} of arguments for \ab{f}, and a tuple \ab{v} \as{:} \aof{∥} \ab{𝑆}
\aof{∥} \ab{g} \as{→} \ab{A} of arguments for \ab{g}, and if we know that \ab f is identically equal to
\ab{g}---that is, \ab{f} \aod{≡} \ab{g} (intensionally)---then we should be able to
check whether \ab u and \ab v are pointwise equal.  Technically, though, \ab{u} and
\ab{v} inhabit different types, so, in order to compare them, we must convince Agda
that \ab u and \ab v inhabit the same type. Of course, this requires an appeal to the
hypothesis \ab f \aod{≡} \ab g, as we see in the definition of \af{EqArgs} below (adapted
from Andreas Abel's development~\cite{Abel:2021}), which neatly resolves this minor
technicality.

\begin{code}

EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (arity 𝑆 f → Carrier ξ) → (arity 𝑆 g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)

EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )

\end{code}

Finally, we are ready to define an operator which
translates an ordinary (algebraic) signature into a signature of algebras over setoids.
\ifshort\else
We denote this operator by \aof{⟨\AgdaUnderscore{}⟩} and define it as follows.
\fi

\begin{code}

⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid (𝓞 ⊔ 𝓥 ⊔ α) (𝓞 ⊔ 𝓥 ⊔ ρᵃ)

Carrier  (⟨ 𝑆 ⟩ ξ)                = Σ[ f ∈ ops 𝑆 ] (arity 𝑆 f → ξ .Carrier)
_≈ˢ_     (⟨ 𝑆 ⟩ ξ)(f , u)(g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

reflᵉ   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → reflˢ   ξ
symᵉ    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → symˢ    ξ (g i)
transᵉ  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → transˢ  ξ (g i) (h i)
\end{code}

%% -----------------------------------------------------------------------------
\subsection{Algebras}\label{algebras}
Informally, an \defn{algebraic structure in the signature} \ab{𝑆} = (\ab{F}, \ab{ρ}), or
\ab{𝑆}-\defn{algebra}, is denoted by \ab{𝑨} = (\ab{A}, \ab{Fᴬ}) and consists of
\begin{itemize}
\item a \emph{nonempty} set (or type) \ab A, called the \defn{domain} (or \defn{carrier} or
\defn{universe}) of the algebra;
\item a collection \ab{Fᴬ} :=
  \{ \ab{fᴬ} \as{∣} \ab f \as{∈} \ab F, \ab{fᴬ} \as :
    (\ab{ρ} \ab f \as{→} \ab A) \as{→} \ab A \} of \defn{operations} on \ab{A};
\item a (potentially empty) collection of \defn{identities} satisfied by elements and
operations of \ab{𝑨}.
\end{itemize}
The \agdaalgebras library represents algebras as inhabitants of a record type with two
fields:\footnote{We postpone introducing identities until~§\ref{equational-logic}.}
\begin{itemize}
\item \afld{Domain}, representing the domain of the algebra;
\item \afld{Interp}, representing the \emph{interpretation} in the algebra of each
operation symbol in \ab{𝑆}.
\end{itemize}
The \afld{Domain} is a setoid whose \afld{Carrier} denotes the domain of the algebra and
whose equivalence relation denotes equality of elements of the domain.

Here is the definition of the \ar{Algebra} type followed by an explanation of how the
standard library's \ar{Func} type is used to represent the interpretation of operation
symbols in an algebra.

\begin{code}
module _ (𝑆 : Signature 𝓞 𝓥) where
  record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
   constructor alg
   field  Domain  : Setoid α ρ
          Interp  : ⟨ 𝑆 ⟩ Domain ⟶ Domain

\end{code}
We define a bit of syntactic sugar for readability.
If \ab{𝑨} is an algebra, then
\begin{itemize}
\item \aof{𝔻[ \ab{𝑨} ]} denotes the setoid \afld{Domain} \ab{𝑨},
\item \aof{𝕌[ \ab{𝑨} ]} is the underlying carrier of the algebra \ab{𝑨}, and
\item \ab f \aof{̂} \ab{𝑨} denotes the interpretation in the algebra \ab{𝑨} of the operation symbol \ab f.
\end{itemize}
\begin{code}
open Algebra

module _ {𝑆 : Signature 𝓞 𝓥} where
  𝔻[_] : Algebra 𝑆 α ρᵃ →  Setoid α ρᵃ
  𝔻[ 𝑨 ] = Domain 𝑨
  𝕌[_] : Algebra 𝑆 α ρᵃ → Type α
  𝕌[ 𝑨 ] = Carrier (Domain 𝑨)
  _̂_ : (f : ops 𝑆 )(𝑨 : Algebra 𝑆 α ρᵃ) → (arity 𝑆 f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
  f ̂ 𝑨 = λ a → Interp 𝑨 ⟨$⟩ (f , a)
\end{code}

%% -----------------------------------------------------------------------------
\paragraph*{Universe levels of algebra types}
The hierarchy of type universes in \agda is structured as follows:
\ap{Type} \ab{ℓ} : \ap{Type} (\ap{lsuc} \ab{ℓ}), \ap{Type} (\ap{lsuc} \ab{ℓ}) : \ap{Type}
(\ap{lsuc} (\ap{lsuc} \ab{ℓ})), …. This means that \ap{Type} \ab{ℓ} has type \ap{Type}
(\ap{lsuc} \ab{ℓ}), etc.  However, this does \emph{not} imply that \ap{Type} \ab{ℓ} :
\ap{Type} (\ap{lsuc} (\ap{lsuc} \ab{ℓ})). In other words, \agda's universe hierarchy is
\emph{noncumulative}.
\ifshort
An
\else
This can be advantageous as it becomes possible to treat universe
levels more generally and precisely. On the other hand, an
\fi
unfortunate side-effect of this noncumulativity is that it can sometimes seem unreasonably
difficult to convince \agda that a program or proof is correct.
\ifshort\else
This aspect of the language was one of the few stumbling
blocks we encountered while learning how to use \agda for formalizing universal algebra in
type theory. Although some may consider this to be one of the least interesting and most
technical aspects of this paper, others might find the presentation more helpful if we
resist the urge to gloss over these technicalities.
\fi
Therefore, it seems worthwhile to explain how we make use
of the general universe lifting and lowering functions, available in the \agdastdlib, to
develop domain-specific tools for dealing with \agda's noncumulative universe hierarchy.

The current library tries to be as size-polymorphic as possible, and currently encounters
some issues with respect to that. One approach is to use \emph{lifting} to embed
algebras into higher universes. We can lift either or both universe parameters.
\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra 𝑆 α ρᵃ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )
 open Level
 Lift-Algˡ : (ℓ : Level) → Algebra 𝑆 (α ⊔ ℓ) ρᵃ
 Domain (Lift-Algˡ ℓ) =
  record  { Carrier        = Lift ℓ 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → lower x ≈ lower y
          ; isEquivalence  = record { refl = refl ; sym = sym ; trans = trans }}

 Interp (Lift-Algˡ ℓ) ⟨$⟩ (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
 cong (Interp (Lift-Algˡ ℓ)) (≡.refl , lab) = cong (Interp 𝑨) ((≡.refl , lab))

 Lift-Algʳ : (ℓ : Level) → Algebra 𝑆 α (ρᵃ ⊔ ℓ)
 Domain (Lift-Algʳ ℓ) =
  record  { Carrier        = 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → Lift ℓ (x ≈ y)
          ; isEquivalence  = record  { refl  = lift refl
                                     ; sym   = lift ∘ sym ∘ lower
                                     ; trans = λ x y → lift (trans (lower x)(lower y)) }}

 Interp (Lift-Algʳ ℓ ) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (Lift-Algʳ ℓ))(≡.refl , lab) = lift(cong(Interp 𝑨)(≡.refl , λ i → lower (lab i)))

Lift-Alg : {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra 𝑆 α ρᵃ)(ℓ₀ ℓ₁ : Level) → Algebra 𝑆 (α ⊔ ℓ₀) (ρᵃ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁

\end{code}

This lifting operation would be worthless without
a useful semantic connection between the input and output algebras.
Fortunately, it is easy to prove that \af{Lift-Alg} is an \defn{algebraic invariant},
which is to say that the resulting ``lifted'' algebra has the same algebraic properties as
the original algebra, a fact we will codify later in a type called \af{Lift-≅}.

\paragraph*{Product Algebras}
Here we review the (informal) definition of the \defn{product} of a family of
\ab{𝑆}-algebras and then define a type which formalizes this notion in \agda.
Let \ab{ι} be a universe and \ab I~:~\ap{Type}~\ab{ι} a type (the ``indexing type'').
Then the dependent function type \ab{𝒜}~:~\ab
I~\as{→}~\ab{Algebra}~\ab{α}~\ab{ρᵃ} represents an \defn{indexed family of algebras}.
Denote by \af{⨅}~\ab{𝒜} the \defn{product of algebras} in \ab{𝒜} (or \defn{product
algebra}), by which we mean the algebra whose domain is the Cartesian product \af{Π}~\ab
i~꞉~\ab I~\af{,}~\aof{𝔻[~\ab{𝒜}~\ab i~]} of the domains of the algebras in \ab{𝒜}, and
whose operations are those arising by pointwise interpretation in the obvious way: if
\ab{f} is a \ab J-ary operation symbol and if
\ab a~:~\af{Π}~\ab i~꞉~\ab I~\af{,}~\ab J~\as{→}~\aof{𝔻[~\ab{𝒜}~\ab i~]} is, for each
\ab i~:~\ab I, a \ab J-tuple of elements of the domain \aof{𝔻[~\ab{𝒜}~\ab i~]}, then
we define the interpretation of \ab f in \af{⨅}~\ab{𝒜} by\\[-2mm]

(\ab{f}~\af{̂}~\af{⨅}~\ab{𝒜}) \ab a := \as{λ}~(\ab i~:~\ab I)~\as{→}
(\ab{f}~\af{̂}~\ab{𝒜}~\ab i)(\ab{a}~\ab i).\\[8pt]
In the \agdaalgebras library we define the function \af{⨅} which formalizes this
notion of \defn{product algebra} in \mltt.
\begin{code}
module _ {ι : Level}{I : Type ι } where
 ⨅ : {𝑆 : Signature 𝓞 𝓥} (𝒜 : I → Algebra 𝑆 α ρᵃ) → Algebra 𝑆 (α ⊔ ι) (ρᵃ ⊔ ι)
 Domain (⨅ 𝒜) =
  record { Carrier = ∀ i → 𝕌[ 𝒜 i ]
         ; _≈_ = λ a b → ∀ i → (_≈ˢ_ 𝔻[ 𝒜 i ]) (a i)(b i)
         ; isEquivalence =
            record  { refl   = λ i →      reflᵉ   (isEquivalence 𝔻[ 𝒜 i ])
                    ; sym    = λ x i →    symᵉ    (isEquivalence 𝔻[ 𝒜 i ])(x i)
                    ; trans  = λ x y i →  transᵉ  (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i) }}
 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong (Interp (𝒜 i)) (≡.refl , flip f=g i )
\end{code}

%% -------------------------------------------------------------------------------------
\subsection{Homomorphisms}\label{homomorphisms}
Throughout this section, and the rest of the paper unless stated otherwise, \ab{𝑨} and \ab{𝑩}
will denote \ab{𝑆}-algebras inhabiting the types \af{Algebra} \ab{α} \ab{ρᵃ} and
\af{Algebra} \ab{β} \ab{ρᵇ}, respectively.

A \defn{homomorphism} (or ``hom'') from
\ab{𝑨} to \ab{𝑩} is a setoid function \ab{h}~:~\aof{𝔻[~\ab{𝑨}~]} \aor{⟶} \aof{𝔻[~\ab{𝑩}~]}
that is \defn{compatible} with all basic operations; that is, for
every operation symbol \ab{f} : \af{∣~\ab{𝑆}~∣} and all tuples
\ab{a} : \af{∥~\ab{𝑆}~∥}~\ab{f} \as{→} \aof{𝕌[~\ab{𝑨}~]}, we have \ab{h} \aofld{⟨\$⟩}
(\ab{f}~\af{̂}~\ab{𝑨}) \ab{a} \af{≈}
(\ab{f}~\af{̂}~\ab{𝑩}) \ab{h} \aofld{⟨\$⟩} (\ab{a} \au{}).

The type \af{compatible-map} then says that a setoid function respects all
operations, i.e. commutes with all operation symbols.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra 𝑆 α ρᵃ)(𝑩 : Algebra 𝑆 β ρᵇ) where

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map h = ∀ {f : ops 𝑆} {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

\end{code}
We define a synonymous single-field record that captures the idea that
being compatible is exactly what makes a homomorphism. The reason for the
record is to help \agda's inference machinery.

To avoid tuple shenanigans, which mathematicians are overly fond of, \af{hom} is
also defined as a record.
\begin{code}

 record IsHom  (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Set (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ) where
  constructor mkhom
  field
    compatible : compatible-map h

 record Hom : Set (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ) where
   constructor hom
   field
     homf : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]
     isHom : IsHom homf

\end{code}

A \defn{monomorphism} (resp. \defn{epimorphism}) is an injective (resp. surjective)
homomorphism.
\begin{code}

 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  constructor ismon
  field  isHom : IsHom h
         isInjective : IsInjective h

  HomReduct : Hom
  HomReduct = hom h isHom

 record Mon : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ) where
   constructor mon
   field
     monf : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]
     isMon : IsMon monf

 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
  constructor isepi
  field  isHom : IsHom h
         isSurjective : IsSurjective h

  HomReduct : Hom
  HomReduct = hom h isHom

 record Epi : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ) where
   constructor epi
   field
     epif : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]
     isEpi : IsEpi epif
\end{code}

We also want to be able to apply one of these 'directly'.
\begin{code}
_$ʰ_ : {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ} {𝑩 : Algebra 𝑆 β ρᵇ} → Hom 𝑨 𝑩 → 𝕌[ 𝑨 ] → 𝕌[ 𝑩 ]
h $ʰ a = Hom.homf h ⟨$⟩ a

\end{code}

\paragraph*{Composition of homomorphisms}
The composition of homomorphisms is again a homomorphism, and similarly for epimorphisms (and monomorphisms).
\ifshort
The proofs of these facts are straightforward so we omit them, but give them names,
\af{∘-hom} and \af{∘-epi}, so we can refer to them below.
\else

\begin{code}

module _  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ} {𝑩 : Algebra 𝑆 β ρᵇ} {𝑪 : Algebra 𝑆 γ ρᶜ}
          {g : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]}{h : 𝔻[ 𝑩 ] ⟶ 𝔻[ 𝑪 ]} where

  open Setoid 𝔻[ 𝑪 ] using ( trans )
  open IsHom ; open IsEpi

  ∘-is-hom : IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-hom (mkhom gh) (mkhom hh) = mkhom (trans (cong h gh) hh)

  ∘-is-epi : IsEpi 𝑨 𝑩 g → IsEpi 𝑩 𝑪 h → IsEpi 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-epi (isepi gE gS) (isepi hE hS) = isepi (∘-is-hom gE hE) (∘-IsSurjective g h gS hS)

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ} {𝑩 : Algebra 𝑆 β ρᵇ} {𝑪 : Algebra 𝑆 γ ρᶜ} where

  ∘-hom : Hom 𝑨 𝑩 → Hom 𝑩 𝑪  → Hom 𝑨 𝑪
  ∘-hom (hom h hhom) (hom g ghom) = hom (g ⟨∘⟩ h) (∘-is-hom hhom ghom)

  ∘-epi : Epi 𝑨 𝑩 → Epi 𝑩 𝑪  → Epi 𝑨 𝑪
  ∘-epi (epi h hepi) (epi g gepi) = epi (g ⟨∘⟩ h) (∘-is-epi hepi gepi)
\end{code}

\paragraph*{Universe lifting of homomorphisms}
Here we define the identity homomorphism for setoid algebras. Then we prove that the
operations of lifting and lowering of a setoid algebra are homomorphisms.

\begin{code}

𝒾𝒹 : {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ} → Hom 𝑨 𝑨
𝒾𝒹 {𝑨 = 𝑨} = hom 𝑖𝑑 (mkhom (Setoid.reflexive 𝔻[ 𝑨 ] ≡.refl))

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}{ℓ : Level} where
 open Setoid 𝔻[ 𝑨 ]              using ( reflexive )  renaming ( _≈_ to _≈₁_ ; refl to refl₁ )
 open Setoid 𝔻[ Lift-Algˡ 𝑨 ℓ ]  using ()             renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
 open Setoid 𝔻[ Lift-Algʳ 𝑨 ℓ ]  using ()             renaming ( _≈_ to _≈ʳ_ ; refl to reflʳ)
 open Level
 open Hom

 ToLiftˡ : Hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
 ToLiftˡ = hom record { f = lift ; cong = id } (mkhom (reflexive ≡.refl))

 FromLiftˡ : Hom (Lift-Algˡ 𝑨 ℓ) 𝑨
 FromLiftˡ = hom record { f = lower ; cong = id } (mkhom reflˡ)

 ToFromLiftˡ : ∀ b → ToLiftˡ $ʰ (FromLiftˡ $ʰ b) ≈ˡ b
 ToFromLiftˡ b = refl₁

 FromToLiftˡ : ∀ a → FromLiftˡ $ʰ (ToLiftˡ $ʰ a) ≈₁ a
 FromToLiftˡ a = refl₁

 ToLiftʳ : Hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
 ToLiftʳ = hom record { f = id ; cong = lift } (mkhom (lift (reflexive ≡.refl)))

 FromLiftʳ : Hom (Lift-Algʳ 𝑨 ℓ) 𝑨
 FromLiftʳ = hom record { f = id ; cong = lower } (mkhom reflˡ)

 ToFromLiftʳ : ∀ b → ToLiftʳ $ʰ (FromLiftʳ $ʰ b) ≈ʳ b
 ToFromLiftʳ b = lift refl₁

 FromToLiftʳ : ∀ a → FromLiftʳ $ʰ (ToLiftʳ $ʰ a) ≈₁ a
 FromToLiftʳ a = refl₁

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}{ℓ r : Level} where
 open  Setoid 𝔻[ 𝑨 ]               using ( refl )
 open  Setoid 𝔻[ Lift-Alg 𝑨 ℓ r ]  using ( _≈_ )
 open  Level
 open Hom

 ToLift : Hom 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift = ∘-hom ToLiftˡ ToLiftʳ

 FromLift : Hom (Lift-Alg 𝑨 ℓ r) 𝑨
 FromLift = ∘-hom FromLiftʳ FromLiftˡ

 ToFromLift : ∀ b → ToLift $ʰ (FromLift $ʰ b) ≈ b
 ToFromLift b = lift refl

 ToLift-epi : Epi 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift-epi = epi (homf ToLift) (isepi (isHom ToLift) (λ y → lower y , ToFromLift y))
\end{code}

\paragraph*{Homomorphisms of product algebras}
Suppose we have an algebra \ab{𝑨}, a type \ab I : \ap{Type} \ab{𝓘}, and a family \ab{ℬ} :
\ab I \as{→} \ar{Algebra} \ab{β} \ab{ρᵇ} of algebras.
We sometimes refer to the inhabitants of \ab{I} as \emph{indices}, and call \ab{ℬ} an
\defn{indexed family of algebras}. If in addition we have a family \ab{𝒽} : (\ab i : \ab
I) → \af{hom} \ab{𝑨} (\ab{ℬ} \ab i) of homomorphisms, then we can construct a homomorphism
from \ab{𝑨} to the product \af{⨅} \ab{ℬ} in the natural way.  We codify the latter in
dependent type theory as follows.

\begin{code}

module _ {ι : Level}{I : Type ι}{𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}(ℬ : I → Algebra 𝑆 β ρᵇ)  where
 open IsHom ; open Hom

 ⨅-hom-co : (∀(i : I) → Hom 𝑨 (ℬ i)) → Hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = hom h hhom
  where
  h : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ ℬ ]
  h ⟨$⟩ a = λ i → (𝒽 i) $ʰ a
  cong h xy i = cong (homf (𝒽 i)) xy
  hhom : IsHom 𝑨 (⨅ ℬ) h
  hhom = mkhom λ i → compatible (isHom (𝒽 i))
\end{code}

\paragraph*{Factorization of homomorphisms}
\fi      %%% END LONG VERSION ONLY SECTION
Another basic fact about homomorphisms that we formalize in the \agdaalgebras library
(as the type \af{HomFactor}) is the following factorization theorem: if \ab g : \af{hom}
\ab{𝑨} \ab{𝑩}, \ab h : \af{hom} \ab{𝑨} \ab{𝑪}, \ab h is surjective, and \af{ker} \ab h
\aof{⊆} \af{ker} \ab g, then there exists \ab{φ} : \af{hom} \ab{𝑪} \ab{𝑩} such that \ab g
= \ab{φ} \aof{∘} \ab h.
\ifshort\else

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}(𝑩 : Algebra 𝑆 β ρᵇ){𝑪 : Algebra 𝑆 γ ρᶜ}
         (gh : Hom 𝑨 𝑩)(hh : Hom 𝑨 𝑪) where
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈₂_ )
 open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈₃_ )
 open Hom ; open IsHom
 private gfunc = homf gh ; g = _⟨$⟩_ gfunc ; hfunc = homf hh ; h = _⟨$⟩_ hfunc

 HomFactor :  ker hfunc ⊆ ker gfunc
  →           IsSurjective hfunc
  →           Σ[ φ ∈ Hom 𝑪 𝑩 ] ∀ a → g a ≈₂ φ $ʰ h a
 HomFactor Khg hE = (hom φ (mkhom φcomp)) , gφh
  where
  h⁻¹ : 𝕌[ 𝑪 ] → 𝕌[ 𝑨 ]
  h⁻¹ = SurjInv hfunc hE

  η : ∀ {c} → h (h⁻¹ c) ≈₃ c
  η {c} = snd (hE c)

  open Setoid 𝔻[ 𝑪 ] using ( sym ; trans )
  ζ : ∀{x y} → x ≈₃ y → h (h⁻¹ x) ≈₃ h (h⁻¹ y)
  ζ xy = trans η (trans xy (sym η))

  φ : 𝔻[ 𝑪 ] ⟶ 𝔻[ 𝑩 ]
  φ = record { f = g ∘ h⁻¹ ; cong = Khg ∘ ζ }

  gφh : (a : 𝕌[ 𝑨 ]) → g a ≈₂ φ ⟨$⟩ h a
  gφh a = Khg (sym η)

  φcomp : compatible-map 𝑪 𝑩 φ
  φcomp {f}{c} =
   begin
    φ    ⟨$⟩  (f ̂ 𝑪)                   c       ≈˘⟨  cong φ (cong (Interp 𝑪) (≡.refl , λ _ → η))  ⟩
    g(h⁻¹(    (f ̂ 𝑪)  (h ∘    h⁻¹  ∘  c  )))   ≈˘⟨  cong φ (compatible (isHom hh))               ⟩
    g(h⁻¹(h(  (f ̂ 𝑨)  (       h⁻¹  ∘  c  ))))  ≈˘⟨  gφh ((f ̂ 𝑨)(h⁻¹ ∘ c))                       ⟩
    g(        (f ̂ 𝑨)  (       h⁻¹  ∘  c  ))    ≈⟨   compatible (isHom gh)                        ⟩
              (f ̂ 𝑩)  (g ∘ (  h⁻¹  ∘  c  ))    ∎ where open SetoidReasoning 𝔻[ 𝑩 ]
\end{code}
\paragraph*{Isomorphisms}
\fi      %%% END LONG VERSION ONLY SECTION

Two structures are \defn{isomorphic} provided there are homomorphisms from each to the
other that compose to the identity. In the \agdaalgebras library we codify this notion as
well as some of its obvious consequences, as a record type called \ar{\au{}≅\au{}}.
\ifshort
Here we display only the essential part of the definition, but \seemedium.
\else

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra 𝑆 α ρᵃ) (𝑩 : Algebra 𝑆 β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ] using () renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᴮ_ )
 open Hom
\end{code}
\fi
\begin{code}

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ ) where
  constructor  mkiso
  field
    to : Hom 𝑨 𝑩
    from : Hom 𝑩 𝑨
    to∼from : ∀ b → to   $ʰ (from $ʰ b)  ≈ᴮ b
    from∼to : ∀ a → from $ʰ (to   $ʰ a)  ≈ᴬ a
\end{code}
\ifshort\else    %%% BEGIN LONG VERSION ONLY
\begin{code}

  toIsInjective : IsInjective (homf to)
  toIsInjective {x}{y} xy = begin
    x                  ≈˘⟨ from∼to x ⟩
    from $ʰ (to $ʰ x)  ≈⟨ cong (homf from) xy ⟩
    from $ʰ (to $ʰ y)  ≈⟨ from∼to y ⟩
    y                  ∎
   where open SetoidReasoning 𝔻[ 𝑨 ]

open _≅_

\end{code}

It is easy to prove that \ar{\au{}≅\au{}} is an equivalence relation, as follows.

\begin{code}
module _ {𝑆 : Signature 𝓞 𝓥} where
  open Hom
  ≅-refl : Reflexive (_≅_ {α = α}{ρᵃ}{𝑆 = 𝑆})
  ≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl where open Setoid 𝔻[ 𝑨 ] using ( refl )

  ≅-sym : Sym (_≅_{α = β}{ρᵇ}{𝑆 = 𝑆}) (_≅_{_}{α = α}{ρᵃ})
  ≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

  ≅-trans : Trans (_≅_ {α = α}{ρᵃ}) (_≅_{α = β}{ρᵇ}) (_≅_{α = α}{ρᵃ}{γ}{ρᶜ})
  ≅-trans {ρᶜ = ρᶜ} {𝑨} {𝑩} {𝑪} (mkiso to₁ from₁ to∼from₁ from∼to₁) (mkiso to₂ from₂ to∼from₂ from∼to₂) =
    mkiso f g f∘g∼id g∘f∼id
   where
    f = ∘-hom {𝑆 = 𝑆} to₁ to₂
    g = ∘-hom from₂ from₁

    open Setoid 𝔻[ 𝑨 ] using (_≈_; trans)
    open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈ᶜ_ ; trans to transᶜ )

    f∘g∼id : ∀ b → f $ʰ (g $ʰ b) ≈ᶜ b
    f∘g∼id b = transᶜ (cong (homf to₂) (to∼from₁ _)) (to∼from₂ b)

    g∘f∼id : ∀ a → g $ʰ (f $ʰ a) ≈ a
    g∘f∼id a = trans (cong (homf from₁) (from∼to₂ _)) (from∼to₁ a)
\end{code}
\fi

\paragraph*{Lift-Alg is an algebraic invariant}
The \af{Lift-Alg} operation neatly resolves the technical problem arising from the
noncumulativity of \agda's universe hierarchy. It does so without changing the algebraic
semantics because isomorphism classes of algebras are closed under \af{Lift-Alg}.
\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ Lift-Algˡ 𝑨 ℓ
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})
 Lift-≅ʳ : 𝑨 ≅ Lift-Algʳ 𝑨 ℓ
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ
\end{code}

\paragraph*{Homomorphic images}
Here we describe what we have found to be the most useful
way to represent the class of \emph{homomorphic images} of an algebra in \mltt.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} where
 _IsHomImageOf_ : (𝑩 : Algebra 𝑆 β ρᵇ)(𝑨 : Algebra 𝑆 α ρᵃ) → Type _
 𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ Hom 𝑨 𝑩 ] IsSurjective (Hom.homf φ)

 IdHomImage : {𝑨 : Algebra 𝑆 α ρᵃ} → 𝑨 IsHomImageOf 𝑨
 IdHomImage {𝑨 = 𝑨} = 𝒾𝒹 , λ y → y , reflˢ 𝔻[ 𝑨 ]
\end{code}

%% -------------------------------------------------------------------------------------
\subsection{Subalgebras}
\label{subalgebras}
Given \ab{𝑆}-algebras \ab{𝑨} and \ab{𝑩}, we say that \ab{𝑨} is a \defn{subalgebra} of
\ab{𝑨} and write \ab{𝑨}~\aof{≤}~\ab{𝑩} just in case \ab{𝑨} can be \emph{homomorphically
embedded} in \ab{𝑩}; in other terms, \ab{𝑨}~\aof{≤}~\ab{𝑩} iff there exists an injective
homomorphism from \ab{𝑨} to \ab{𝑩}. The following definition codifies the \defn{binary
subalgebra relation}, \aof{\au{}≤\au{}}, on the class of \ab{𝑆}-algebras.

\begin{code}

 record _≤_ (𝑨 : Algebra 𝑆 α ρᵃ) (𝑩 : Algebra 𝑆 β ρᵇ) : Type (α ⊔ ρᵃ ⊔ 𝓞 ⊔ 𝓥 ⊔ β ⊔ ρᵇ) where
   constructor subAlg
   field
     hom≤ : Hom 𝑨 𝑩
     isinj : IsInjective (Hom.homf hom≤)

open _≤_

\end{code}
Obviously the subalgebra relation is reflexive by the identity monomorphism; it is also
transitive since composition of monomorphisms is a monomorphism.
\begin{code}

≤-reflexive   :  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive {𝑨 = 𝑨} = subAlg 𝒾𝒹 id

≤-transitive  :  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}{𝑩 : Algebra 𝑆 β ρᵇ}{𝑪 : Algebra 𝑆 γ ρᶜ}
 →               𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
≤-transitive ( subAlg f finj ) ( subAlg g ginj ) = subAlg (∘-hom f g ) (∘-IsInjective (Hom.homf f) (Hom.homf g) finj ginj)
\end{code}

\noindent If
\ab{𝒜} : \ab I → \af{Algebra} \ab{α} \ab{ρᵃ},
\ab{ℬ} : \ab I → \af{Algebra} \ab{β} \ab{ρᵇ} (families of \ab{𝑆}-algebras) and
\ab{ℬ} \ab i \af{≤} \ab{𝒜} \ab i for all \ab i~:~\ab I, then \af{⨅} \ab{ℬ} is a subalgebra
of \af{⨅} \ab{𝒜}.

Here is how we express this fact in \agda.
\begin{code}
module _ {𝑆 : Signature 𝓞 𝓥} {ι : Level} {I : Type ι}{𝒜 : I → Algebra 𝑆 α ρᵃ}{ℬ : I → Algebra 𝑆 β ρᵇ} where
 open Hom ; open IsHom

 ⨅-≤ : (∀ i → ℬ i ≤ 𝒜 i) → ⨅ ℬ ≤ ⨅ 𝒜
 ⨅-≤ B≤A = subAlg (hom hfunc hhom) hM
  where
  hi : ∀ i → Hom (ℬ i) (𝒜 i)
  hi = hom≤ ∘ B≤A
  hfunc : 𝔻[ ⨅ ℬ ] ⟶ 𝔻[ ⨅ 𝒜 ]
  (hfunc ⟨$⟩ x) i = homf (hi i) ⟨$⟩ x i
  cong hfunc = λ xy i → cong (homf (hi i)) (xy i)
  hhom : IsHom (⨅ ℬ) (⨅ 𝒜) hfunc
  hhom = mkhom λ i → compatible (isHom (hi i))
  hM : IsInjective hfunc
  hM = λ xy i → isinj (B≤A i) (xy i)

\end{code}

We conclude this brief subsection on subalgebras
\ifshort
by mentioning the function \af{mon→≤}, which we apply once below; it merely converts a monomorphism into a pair in \aof{≤}.
\else
with two easy facts
that will be useful later. The first merely converts a monomorphism into a pair in the subalgebra relation
while the second is an algebraic invariance property of \aof{≤}.

\begin{code}

mon→≤      :  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}{𝑩 : Algebra 𝑆 β ρᵇ} → Mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨} {𝑩} (mon monf record { isHom = isHom ; isInjective = isInjective }) = subAlg (hom monf isHom) isInjective

≅-trans-≤  :  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 α ρᵃ}{𝑩 : Algebra 𝑆 β ρᵇ}{𝑪 : Algebra 𝑆 γ ρᶜ}
 →            𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
≅-trans-≤ A≅B (subAlg h hinj) = subAlg (∘-hom (to A≅B) h) (∘-IsInjective (Hom.homf (to A≅B)) (Hom.homf h) (toIsInjective A≅B) hinj)
\end{code}
\fi

%% -------------------------------------------------------------------------------------

\subsection{Terms}
\label{terms}
Fix a signature \ab{𝑆} and let \ab X denote an arbitrary nonempty collection of variable
symbols. Such a collection of variable symbols is called a \defn{context}.
Assume the symbols in \ab X are distinct from the operation symbols of
\ab{𝑆}, that is \ab X \aof{∩} \aof{∣} \ab{𝑆} \aof{∣} = ∅.
A \defn{word} in the language of \ab{𝑆} is a finite sequence of members of \ab X \aof{∪}
\aof{∣~\ab{𝑆}~∣}. We denote the concatenation of such sequences by simple juxtaposition.
Let \ab{S₀} denote the set of nullary operation symbols of \ab{𝑆}. We define by induction
on \ab n the sets \ab{𝑇ₙ} of \emph{words} over \ab X \aof{∪} \aof{∣~\ab{𝑆}~∣} as
follows (cf.~\cite[Def. 4.19]{Bergman:2012}): \ab{𝑇₀} := \ab X \aof{∪} \ab{S₀} and
\ab{𝑇ₙ₊₁} := \ab{𝑇ₙ} \aof{∪} \ab{𝒯ₙ}, where \ab{𝒯ₙ} is the collection of all \ab f \ab t
such that \ab f : \aof{∣~\ab{𝑆}~∣} and \ab t : \aof{∥~\ab{𝑆}~∥} \ab f \as{→}
\ab{𝑇ₙ}.
\ifshort\else
(Recall, \aof{∥~\ab{𝑆}~∥} \ab f is the arity of the operation symbol \ab f.)
\fi
An \ab{𝑆}-\defn{term} is a term in the language of \ab{𝑆} and the collection of all
\ab{𝑆}-\defn{terms} in the context \ab X is given by \Term{X} := \aof{⋃ₙ} \ab{𝑇ₙ}.

As even its informal definition of \Term{X} is recursive, it should come as no surprise
that the semantics of terms can be usefully represented in type theory as an inductive
type. Indeed, here is such a representation.

\begin{code}

data Term (𝑆 : Signature 𝓞 𝓥) (X : Type χ ) : Type (𝓞 ⊔ 𝓥 ⊔ lsuc χ)  where
 ℊ : X → Term 𝑆 X
 node : (f : ops 𝑆)(t : arity 𝑆 f → Term 𝑆 X) → Term 𝑆 X

\end{code}
This basic inductive type represents each term as a tree with an operation symbol at each
\aic{node} and a variable symbol at each leaf \aic{ℊ}%
\ifshort
.
\else
; hence the constructor names
(\aic{ℊ} for ``generator'' and \aic{node} for ``node'').
\fi

\paragraph*{The term algebra}
We enrich the \ad{Term} type with
an inductive type \ad{\au{}≃\au{}} representing equality of terms, then we roll up
into a setoid the types \ad{Term} and \ad{\au{}≃\au{}} along with a proof that
\ad{\au{}≃\au{}} is an equivalence relation. Ultimately we use this setoid of \ab{𝑆}-terms
as the domain of an algebra, called the \emph{term algebra in the signature} \ab{𝑆}.
Here is the equality type on terms.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} {X : Type χ } where
 data _≃_ : Term 𝑆 X → Term 𝑆 X → Type (𝓞 ⊔ 𝓥 ⊔ lsuc χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≃ (ℊ y)
  gnl : ∀ {f}{s t : arity 𝑆 f → Term 𝑆 X} → (∀ i → (s i) ≃ (t i)) → (node f s) ≃ (node f t)

\end{code}
It's easy to show that this is an equivalence relation on terms.

\begin{code}

 ≃-isRefl   : Reflexive      _≃_
 ≃-isRefl {ℊ _} = rfl ≡.refl
 ≃-isRefl {node _ _} = gnl (λ _ → ≃-isRefl)

 ≃-isSym    : Symmetric      _≃_
 ≃-isSym (rfl x) = rfl (≡.sym x)
 ≃-isSym (gnl x) = gnl (λ i → ≃-isSym (x i))

 ≃-isTrans  : Transitive     _≃_
 ≃-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≃-isTrans (gnl x) (gnl y) = gnl (λ i → ≃-isTrans (x i) (y i))

 ≃-isEquiv  : IsEquivalence  _≃_
 ≃-isEquiv = record { refl = ≃-isRefl ; sym = ≃-isSym ; trans = ≃-isTrans }
\end{code}
\fi

We now define, for a given signature \ab{𝑆} and context \ab X,
%if the type \Term{X} is nonempty (equivalently, if \ab X or
%\aof{∣~\ab{𝑆}~∣} is nonempty), then
the algebraic structure \T{X}, known as the \defn{term algebra in} \ab{𝑆} \defn{over} \ab
X.  Terms are viewed as acting on other terms, so both the elements of the domain of \T{X}
and its basic operations are the terms themselves. That is, for each operation symbol \ab
f : \aof{∣~\ab{𝑆}~∣}, we denote by \ab f~\aof{̂}~\T{X} the operation on \Term{X} that maps
each tuple of terms, say, \ab t : \aof{∥~\ab{𝑆}~∥} \ab f \as{→} \Term{X}, to the formal
term \ab f \ab t.
%We let \T{X} denote the term algebra in \ab{𝑆} over \ab X; it has universe \Term{X} and
%operations \ab f \aof{̂} \T{X}, one for each symbol \ab f in \aof{∣~\ab{𝑆}~∣}.
We codify these notions in \agda as follows.

\begin{code}

TermSetoid : (𝑆 : Signature 𝓞 𝓥) (X : Type χ) → Setoid (𝓞 ⊔ 𝓥 ⊔ lsuc χ) (𝓞 ⊔ 𝓥 ⊔ lsuc χ)
TermSetoid 𝑆 X = record { Carrier = Term 𝑆 X ; _≈_ = _≃_ ; isEquivalence = ≃-isEquiv }

𝑻 : (𝑆 : Signature 𝓞 𝓥) (X : Type χ) → Algebra 𝑆 (𝓞 ⊔ 𝓥 ⊔ lsuc χ) (𝓞 ⊔ 𝓥 ⊔ lsuc χ)
𝑻 𝑆 X = alg (TermSetoid 𝑆 X) record
  { f = λ { (f , ts) → node f ts }
  ; cong = λ { (≡.refl , ss≃ts) → gnl ss≃ts }
  }
\end{code}

\paragraph*{Substitution, environments and interpretation of terms}
In this section, we formalize the notions of \emph{substitution}, \emph{environment}, and
\emph{interpretation of terms} in an algebra. The approach to formalizing these concepts,
and the \agda code presented in this subsection, is based on similar code developed by
Andreas Abel to formalize Birkhoff's completeness theorem~\cite{Abel:2021}.

\ifshort\else
Recall that the domain of an algebra \ab{𝑨} is a setoid, which we denote by
\af{𝔻[~\ab{𝑨}~]}, whose \afld{Carrier} is the carrier of the algebra, \af{𝕌[~\ab{𝑨}~]},
and whose equivalence relation represents equality of elements in \af{𝕌[~\ab{𝑨}~]}.
\fi

%Before defining the \af{Env} function (which will depend on a specific algebra) we first
The function \af{Sub} performs substitution from one context to
another.  Specifically, if \ab X and \ab Y are contexts, then \af{Sub} \ab X \ab Y
assigns a term in \ab X to each symbol in \ab Y.
The definition of \af{Sub} is a slight modification of the one given by Andreas Abel
(\textit{op.~cit.}), as is the recursive definition of \af{[~\ab{σ}~]} \ab t,
which denotes a substitution applied to a term.

\begin{code}

Sub : {𝑆 : Signature 𝓞 𝓥} → Type χ → Type χ → Type _
Sub {𝑆 = 𝑆} X Y = Y → Term 𝑆 X

[_]_ : {𝑆 : Signature 𝓞 𝓥} {X Y : Type χ} → Sub X Y → Term 𝑆 Y → Term 𝑆 X
[ σ ] (ℊ x) = σ x
[ σ ] (node f ts) = node f (λ i → [ σ ] (ts i))

\end{code}

Fix a signature \ab{𝑆}, a context \ab X, and an \ab{𝑆}-algebra \ab{𝑨}.
An \defn{environment} for these data consists of the function type \ab X \as{→}
\af{𝕌[~\ab{𝑨}~]} along with an equality on this type.
The function \af{Env} manifests this notion by taking an \ab{𝑆}-algebra \ab{𝑨} and a
context \ab{X} and returning a setoid whose \afld{Carrier} is the type
\ab X~\as{→}~\af{𝕌[~\ab{𝑨}~]} and whose equivalence relation
is pointwise equality of functions in \ab X \as{→} \af{𝕌[~\ab{𝑨}~]}.

\begin{code}

module Environment {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra 𝑆 α ℓ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )
 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                 ; _≈_ = λ ρ τ → (x : X) → ρ x ≈ τ x
                 ; isEquivalence = record  { refl   = λ _      → refl
                                           ; sym    = λ h x    → sym (h x)
                                           ; trans  = λ g h x  → trans (g x)(h x) }}

\end{code}
Notice that this definition, as well as the next, are relative to a certain fixed algebra,
so we put them inside a submodule called \am{Environment}. This allows us to load the
submodule and associate its definitions with a number of different algebras simultaneously.

Next, the recursive function \af{⟦\au{}⟧} denotes \defn{interpretation} of
a term in a given algebra, \emph{evaluated} in a given environment.

\begin{code}

 ⟦_⟧ : {X : Type χ}(t : Term 𝑆 X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧          ⟨$⟩ ρ    = ρ x
 ⟦ node f args ⟧  ⟨$⟩ ρ    = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧         u≈v = u≈v x
 cong ⟦ node f args ⟧ x≈y = cong (Interp 𝑨) (≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

\end{code}
As we end up applying interpretations often, it is useful to have a shorthand.

\begin{code}

 infix 5 _⟦$⟧_
 _⟦$⟧_ : {X : Type χ}(t : Term 𝑆 X) → Setoid.Carrier (Env X) → 𝕌[ 𝑨 ]
 trm ⟦$⟧ ρ = ⟦ trm ⟧ ⟨$⟩ ρ
\end{code}

Two terms interpreted in \ab{𝑨} are proclaimed \defn{equal} if they are equal for all
environments.
\begin{code}

 Equal : {X : Type χ}(s t : Term 𝑆 X) → Type (α ⊔ ℓ ⊔ χ)
 Equal {X = X} s t = ∀ ρ → s ⟦$⟧ ρ ≈ t ⟦$⟧ ρ

 ≃→Equal : {X : Type χ}(s t : Term 𝑆 X) → s ≃ t → Equal s t
 ≃→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≃→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong (Interp 𝑨)(≡.refl , λ i → ≃→Equal (s i) (t i) (x i) ρ)

 EqualIsEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 reflᵉ   EqualIsEquiv = λ _        → refl
 symᵉ    EqualIsEquiv = λ x=y ρ    → sym (x=y ρ)
 transᵉ  EqualIsEquiv = λ ij jk ρ  → trans (ij ρ) (jk ρ)

\end{code}
\fi

The next lemma says that applying a substitution \ab{σ} to a term \ab{t}
and evaluating the result in the environment \ab{ρ} has the same effect as evaluating
\ab{t} the a new environment, specifically, in the environment \as{λ} \ab x \as{→} \aof{⟦~\ab{σ}~\ab{x}~⟧}~\aofld{⟨\$⟩}
\ab{ρ} (see~\cite{Abel:2021} or~\cite[Lem.~3.3.11]{Mitchell:1996}).

\begin{code}

 substitution :  {X Y : Type χ} → (t : Term 𝑆 Y) (σ : Sub X Y) (ρ : Carrier( Env X ) )
  →              [ σ ] t ⟦$⟧ ρ ≈ t ⟦$⟧ (λ x → σ x ⟦$⟧ ρ)
 substitution (ℊ x)        σ ρ = refl
 substitution (node f ts)  σ ρ = cong (Interp 𝑨)(≡.refl , λ i → substitution (ts i) σ ρ)

\end{code}
This concludes the definition of the \am{Environment} module based on~\cite{Abel:2021}.

\ifshort\else
\paragraph*{Compatibility of terms}
\fi
We will need two more facts about term operations.  The first, called
\af{comm-hom-term}, asserts that every term commutes with every homomorphism.  The second,
\af{interp-prod}, shows how to express the interpretation of a term in a product algebra.
\ifshort
We omit the formalization of these facts, but \seeshort for details.
\else

\begin{code}

module _ {X : Type χ}{𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝑆 α ρᵃ}{𝑩 : Algebra 𝑆 β ρᵇ}(hh : Hom 𝑨 𝑩) where
 open Environment 𝑨 using ( _⟦$⟧_ )
 open Environment 𝑩 using () renaming ( _⟦$⟧_ to _⟦$⟧ᴮ_ )
 open Setoid 𝔻[ 𝑩 ] using ( _≈_ ; refl )
 open Hom ; open IsHom
 private h = homf hh ⟨$⟩_
 comm-hom-term : (t : Term 𝑆 X) (a : X → 𝕌[ 𝑨 ]) → h (t ⟦$⟧ a) ≈ t ⟦$⟧ᴮ (h ∘ a)
 comm-hom-term (ℊ x) a       = refl
 comm-hom-term (node f t) a  =
  begin
   h( node f t ⟦$⟧ a)            ≈⟨ compatible (isHom hh) ⟩
   (f ̂ 𝑩)(λ i → h( t i ⟦$⟧ a))  ≈⟨ cong(Interp 𝑩)(≡.refl , λ i → comm-hom-term (t i) a)⟩
   node f t ⟦$⟧ᴮ (h ∘ a)         ∎ where  open SetoidReasoning 𝔻[ 𝑩 ]

module _ {X : Type χ}{ι : Level} {I : Type ι} {𝑆 : Signature 𝓞 𝓥} (𝒜 : I → Algebra 𝑆 α ρᵃ) where
 open Setoid 𝔻[ ⨅ 𝒜 ]  using ( _≈_ )
 open Environment      using ( ⟦_⟧ ; ≃→Equal )
 interp-prod : (p : Term 𝑆 X) → ∀ ρ →  (⟦ ⨅ 𝒜 ⟧ p) ⟨$⟩ ρ   ≈   λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (ρ x) i
 interp-prod (ℊ x)       = λ ρ i  → ≃→Equal (𝒜 i) (ℊ x) (ℊ x) ≃-isRefl λ _ → (ρ x) i
 interp-prod (node f t)  = λ ρ    → cong (Interp (⨅ 𝒜)) ( ≡.refl , λ j k → interp-prod (t j) ρ k )
\end{code}
\fi

\section{Equational Logic}
\label{equational-logic}

\paragraph*{Term identities, equational theories, and the ⊧ relation}
Given a signature \ab{𝑆} and a context \ab X, an \ab{𝑆}-\defn{term equation} or \ab{𝑆}-\defn{term identity}
is an ordered pair (\ab p , \ab q) of 𝑆-terms. For instance, if the context is \ab X :
\ap{Type} \ab{χ}, then a term equation is a pair inhabiting the Cartesian product type
\ad{Term}~\ab{X} \aof{×} \ad{Term}~\ab{X}. Such pairs of terms are also denoted by \ab p \af{≈} \ab
q and are often simply called equations or identities, especially when the signature \ab{𝑆} is obvious.

We define an \defn{equational theory} (or \defn{algebraic theory}) to be a pair \ab{T} =
(\ab{𝑆} , \ab{ℰᵀ}) consisting of a signature \ab{𝑆} and a collection \ab{ℰᵀ} of
\ab{𝑆}-term equations. Some authors reserve the term \defn{theory} for
a \emph{deductively closed} set of equations, that is, a set of equations that is closed
under \emph{entailment} (defined below).

We say that the algebra \ab{𝑨} \emph{satisfies} the equation \ab p \af{≈} \ab q if,
for all \ab{ρ} : \ab X \as{→} \aof{𝔻[~\ab{𝑨}~]},
%(assigning values in the domain of \ab{𝑨} to variable symbols in \ab X)
we have \aof{⟦~\ab{p}~⟧} \aofld{⟨\$⟩} \ab{ρ} \af{≈} \aof{⟦~\ab{q}~⟧} \aofld{⟨\$⟩} \ab{ρ}.
In other words, when they are interpreted in the algebra \ab{𝑨},
the terms \ab{p} and \ab{q} are equal no matter what values in \ab{𝑨} are assigned to variable symbols in \ab{X}.
In this situation, we write
\ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q} and say that \ab{𝑨} \defn{models} \ab{p}~\af{≈}~\ab{q},
or that \ab{𝑨} is a \defn{model} of \ab{p}~\af{≈}~\ab{q}.
If \ab{𝒦} is a class of algebras, all of the same signature, we write \ab{𝒦}~\aof{⊫}~\ab{p}~\aof{≈}~\ab{q}
and say that \ab{𝒦} \defn{models} the identity \ab{p}~\af{≈}~\ab{q} provided for every \ab{𝑨} \aof{∈} \ab{𝒦},
we have \ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q}.

\ifshort\else
\begin{code}
module _ {X : Type χ} {𝑆 : Signature 𝓞 𝓥} where
\end{code}
\fi
\begin{code}

 _⊧_≈_ : Algebra 𝑆 α ρᵃ → Term 𝑆 X → Term 𝑆 X → Type (χ ⊔ α ⊔ ρᵃ)
 𝑨 ⊧ p ≈ q = Environment.Equal 𝑨 p q

 _⊫_≈_ : Pred (Algebra 𝑆 α ρᵃ) ℓ → Term 𝑆 X → Term 𝑆 X → Type (χ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc α ⊔ lsuc ρᵃ ⊔ ℓ)
 𝒦 ⊫ p ≈ q = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}
We represent a set of identities as a predicate over pairs of
terms, say, \ab{ℰ} : \af{Pred}(\ad{Term} \ab{X} \af{×} \ad{Term} \ab{X})~\au{}  and we denote by
\ab{𝑨}~\aof{⊨}~\ab{ℰ} the assertion that the algebra \ab{𝑨} models \ab{p}~\af{≈}~\ab{q}
for all (\ab{p} , \ab{q}) \af{∈} \ab{ℰ}.\footnote{Notice that \af{⊨} is
a stretched version of the models symbol, \af{⊧};
\ifshort\else
this makes it possible for \agda to distinguish and parse expressions involving the types
\af{\au{}⊨\au{}} and \af{\au{}⊧\au{}≈\au{}}.
\fi
In Emacs \texttt{agda2-mode}, the symbol \af{⊨} is produced by typing
\textbackslash\textbar{}=, while \af{⊧} is
produced with \textbackslash{}models.}

Note how the Level of \af{ℰ} is not maximally polymorphic.
\begin{code}

 _⊨_ : (𝑨 : Algebra 𝑆 α ρᵃ) → Pred(Term 𝑆 X × Term 𝑆 X) (𝓞 ⊔ 𝓥 ⊔ lsuc χ) → Type (lsuc χ ⊔ 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ)
 𝑨 ⊨ ℰ = ∀ {p q} → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

\end{code}

If \ab{𝒦} is a class of structures and \ab{ℰ} a set of term identities, then the set of
term equations modeled by \ab{𝒦} is denoted by \af{Th}~\ab{𝒦} and is called the
\defn{equational theory} of \ab{𝒦}, while the class of structures modeling \ab{ℰ} is
denoted by \af{Mod}~\ab{ℰ} and is called the \defn{equational class axiomatized} by
\ab{ℰ}. We formalize these concepts in \agda with the following types.

Note how the definition of \af{Mod} is identical to that of \af{ℰ} but at a different level,
i.e. models are more polymorphic.
\begin{code}

Th : {X : Type χ} {𝑆 : Signature 𝓞 𝓥} → Pred (Algebra 𝑆 α ρᵃ) ℓ → Pred(Term 𝑆 X × Term 𝑆 X) (χ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc α ⊔ lsuc ρᵃ ⊔ ℓ)
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Mod : {X : Type χ} {𝑆 : Signature 𝓞 𝓥} → Pred(Term 𝑆 X × Term 𝑆 X) ℓ → Pred (Algebra 𝑆 α ρᵃ) (lsuc χ ⊔ 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ℓ)
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q
\end{code}

\paragraph*{Entailment}

If \ab{ℰ} is a set of \ab{𝑆}-term equations and \ab{p} and \ab{q} are \ab{𝑆}-terms,
we say that \ab{ℰ} \defn{entails} the equation \ab{p}~\aof{≈}~\ab{q}, and we write
\ab{ℰ}~\ad{⊢}~\ab{p}~\ad{≈}~\ab{q}, just in case every model of \ab{ℰ} also models
\ab{p}~\aof{≈}~\ab{q}.
We represent entailment in type theory using an inductive type that is similar to
the one defined by Abel in~\cite{Abel:2021}.  We call this the \defn{entailment type}
and define it as follows.

\begin{code}

data _⊢_▹_≈_  {𝑆 : Signature 𝓞 𝓥}
              (ℰ : {Y : Type χ} → Pred(Term 𝑆 Y × Term 𝑆 Y) ℓ) :
              (X : Type χ)(p q : Term 𝑆 X) → Type (𝓞 ⊔ 𝓥 ⊔ lsuc χ ⊔ ℓ)  where

 hyp         :  ∀{Y}{p q : Term 𝑆 Y} → (p , q) ∈ ℰ → ℰ ⊢ _ ▹ p ≈ q
 app         :  ∀{Y}{f}{ps qs : arity 𝑆 f → Term 𝑆 Y}
                          → (∀ i → ℰ ⊢ Y ▹ ps i ≈ qs i) → ℰ ⊢ Y ▹ (node f ps) ≈ (node f qs)
 sub         :  ∀{p q}    → ℰ ⊢ Γ ▹ p ≈ q → (σ : Sub Δ Γ) → ℰ ⊢ Δ ▹ ([ σ ] p) ≈ ([ σ ] q)
 reflexive   :  ∀{p}      → ℰ ⊢ Γ ▹ p ≈ p
 symmetric   :  ∀{p q}    → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ p
 transitive  :  ∀{p q r}  → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ r → ℰ ⊢ Γ ▹ p ≈ r

\end{code}

The fact that this type represents the informal semantic notion of entailment
given at the start of this subsection is called \defn{soundness} and
\defn{completeness}.
More precisely, \defn{the entailment type is sound} means the following:
if \ab{ℰ}~\ad{⊢}~\ab{X}~\ad{▹}~\ab p~\ad{≈}~\ab q, then \ab p \aof{≈} \ab q holds in
every model of \ab{ℰ}.
\defn{The entailment type is complete} means the following:
if \ab p \aof{≈} \ab q holds in every model of \ab{ℰ},
then \ab{ℰ}~\ad{⊢}~\ab{X}~\ad{▹}~\ab p~\aof{≈}~\ab q.
Soundness and completeness of an entailment type similar to the one defined above was
proved by Abel in~\cite{Abel:2021}.  We will invoke soundness of the entailment type only once below%
\ifshort
~(by the name \af{sound}), so we omit its proof, but see~\cite{Abel:2021}
or~\cite{DeMeo:2021} for the complete formalization.
\else
; nonetheless, here is its formalization (due to Abel, \textit{op. cit.}):

\begin{code}

module Soundness  {𝑆 : Signature 𝓞 𝓥} (ℰ : {Y : Type χ} → Pred(Term 𝑆 Y × Term 𝑆 Y) (𝓞 ⊔ 𝓥 ⊔ lsuc χ))
                  (𝑨 : Algebra 𝑆 α ρᵃ)               -- We assume an algebra 𝑨
                  (V : ∀{Y} → _⊨_{χ = χ} 𝑨 (ℰ{Y}))  -- that models all equations in ℰ.
                  where
 open SetoidReasoning 𝔻[ 𝑨 ]
 open Environment 𝑨
 sound : ∀ {p q} → ℰ ⊢ Γ ▹ p ≈ q → 𝑨 ⊧ p ≈ q
 sound (hyp i) = V i
 sound (app es) ρ = cong (Interp 𝑨) (≡.refl , λ i → sound (es i) ρ)
 sound (sub {p = p}{q} Epq σ) ρ =
  begin
   [ σ ] p ⟦$⟧                 ρ   ≈⟨   substitution p σ ρ               ⟩
   p       ⟦$⟧ (λ x → σ x ⟦$⟧  ρ)  ≈⟨   sound Epq (λ x → σ x ⟦$⟧ ρ)  ⟩
   q       ⟦$⟧ (λ x → σ x ⟦$⟧  ρ)  ≈˘⟨  substitution q σ ρ               ⟩
   [ σ ] q ⟦$⟧                 ρ   ∎
 sound (reflexive   {p = p}                 ) = reflᵉ   EqualIsEquiv {x = p}
 sound (symmetric   {p = p}{q}     Epq      ) = symᵉ    EqualIsEquiv {x = p}{q}     (sound Epq)
 sound (transitive  {p = p}{q}{r}  Epq Eqr  ) = transᵉ  EqualIsEquiv {i = p}{q}{r}  (sound Epq)(sound Eqr)
\end{code}
\fi

\paragraph*{The Closure Operators H, S, P and V}
Fix a signature \ab{𝑆}, let \ab{𝒦} be a class of \ab{𝑆}-algebras, and define
\begin{itemize}
\item \af H \ab{𝒦} = algebras isomorphic to homomorphic images of members of \ab{𝒦};
\item \af S \ab{𝒦} = algebras isomorphic to subalgebras of a members of \ab{𝒦};
\item \af P \ab{𝒦} = algebras isomorphic to products of members of \ab{𝒦}.
\end{itemize}
\ifshort\else
A straight-forward verification confirms that
\fi
\af H, \af S, and \af P are \emph{closure operators} (expansive, monotone, and
idempotent).  A class \ab{𝒦} of \ab{𝑆}-algebras is said to be \emph{closed under
the taking of homomorphic images} provided \af H \ab{𝒦} \aof{⊆} \ab{𝒦}. Similarly, \ab{𝒦} is
\emph{closed under the taking of subalgebras} (resp., \emph{arbitrary products}) provided
\af S \ab{𝒦} \aof{⊆} \ab{𝒦} (resp., \af P \ab{𝒦} \aof{⊆} \ab{𝒦}). The operators \af H, \af
S, and \af P can be composed with one another repeatedly, forming yet more closure
operators.

% An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to
which it is isomorphic. Thus, the class \af H \ab{𝒦} (resp., \af S \ab{𝒦}; resp., \af P \ab{𝒦}) is closed under isomorphism.

A \emph{variety} is a class of \ab{𝑆}-algebras that is closed under the taking of
homomorphic images, subalgebras, and arbitrary products.  To represent varieties
we define types for the closure operators \af H, \af S, and \af P that are composable; we
then define a type \af V which represents closure under all three of these operators.
Thus, if \ab{𝒦} is a class of \ab{𝑆}-algebras, then
\af V \ab{𝒦} := \af H (\af S (\af P \ab{𝒦})), and \ab{𝒦} is a variety iff \af V \ab{𝒦} \aof{⊆} \ab{𝒦}.
\ifshort\else

We now define the type \af H to represent classes of algebras that include all homomorphic
images of algebras in the class---i.e., classes that are closed under the taking of
homomorphic images---the type \af S to represent classes of algebras that closed under the
taking of subalgebras, and the type \af P to represent classes of algebras closed under the taking of arbitrary products.

\begin{code}

module _ {α ρᵃ β ρᵇ : Level}  where
\end{code}
\fi
\begin{code}

 private 𝒶 = α ⊔ ρᵃ
 H : ∀ ℓ → {𝑆 : Signature 𝓞 𝓥} → Pred(Algebra 𝑆 α ρᵃ) (𝒶 ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) → Pred(Algebra 𝑆 β ρᵇ) (lsuc 𝒶 ⊔ lsuc ℓ ⊔ β ⊔ ρᵇ ⊔ 𝓞 ⊔ 𝓥)
 H _ {𝑆} 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra 𝑆 α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → {𝑆 : Signature 𝓞 𝓥} → Pred (Algebra 𝑆 α ρᵃ) (𝒶 ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) → Pred (Algebra 𝑆 β ρᵇ) (lsuc 𝒶 ⊔ lsuc ℓ ⊔ β ⊔ ρᵇ ⊔ 𝓞 ⊔ 𝓥)
 S _ {𝑆} 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra 𝑆 α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → {𝑆 : Signature 𝓞 𝓥} → Pred(Algebra 𝑆 α ρᵃ) (𝒶 ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) → Pred(Algebra 𝑆 β ρᵇ) (lsuc 𝒶 ⊔ lsuc ℓ ⊔ β ⊔ ρᵇ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ι)
 P _ ι {𝑆} 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra 𝑆 α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) × (𝑩 ≅ ⨅ 𝒜))

\end{code}
Finally, we define the \defn{varietal closure} of a class \ab{𝒦} to be the class \af{V}
\ab{𝒦} := \af{H} (\af{S} (\af{P} \ab{𝒦})).
\ifshort\else
\begin{code}

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} {𝑆 : Signature 𝓞 𝓥} where
\end{code}
\fi
\begin{code}

 private 𝒶 = α ⊔ ρᵃ ; b = β ⊔ ρᵇ
 V : ∀ ℓ ι → Pred(Algebra 𝑆 α ρᵃ) (𝒶 ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) →  Pred(Algebra 𝑆 δ ρᵈ) _
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (𝒶 ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (𝒶 ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))

\end{code}

An important property of the binary relation \aof{⊧} is \emph{algebraic invariance} (i.e.,
invariance under isomorphism).
\ifshort
Here is the formal statement of this property, without proof.
\else
We formalize this property as follows.

\begin{code}

module _ {X : Type χ}{𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝑆 α ρᵃ}(𝑩 : Algebra 𝑆 β ρᵇ)(p q : Term 𝑆 X) where
\end{code}
\fi
\begin{code}

 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q

\end{code}
\ifshort\else
\begin{code}
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ =
  begin
      ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧ (f∼g ∘ ρ)        ⟩
      ⟦ p ⟧   ⟨$⟩ (f  ∘  (g  ∘  ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)  ⟩
    f(⟦ p ⟧ᴬ  ⟨$⟩        (g  ∘  ρ))  ≈⟨   cong (homf fh) (Apq (g ∘ ρ))   ⟩
    f(⟦ q ⟧ᴬ  ⟨$⟩        (g  ∘  ρ))  ≈⟨   comm-hom-term fh q (g ∘ ρ)  ⟩
      ⟦ q ⟧   ⟨$⟩ (f  ∘  (g  ∘  ρ))  ≈⟨   cong ⟦ q ⟧ (f∼g ∘ ρ)        ⟩
      ⟦ q ⟧   ⟨$⟩               ρ    ∎
  where
  open Hom
  private f = _⟨$⟩_ (homf fh) ; g = _⟨$⟩_ (homf gh)
  open Environment 𝑨     using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩     using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑩 ]

\end{code}
\fi
Identities modeled by an algebra \ab{𝑨} are also modeled by every homomorphic image of
\ab{𝑨} and by every subalgebra of \ab{𝑨}.
\ifshort
We refer to these facts as \af{⊧-H-invar} and \af{⊧-S-invar}, but omit their formal
statements and proofs, which are analogous to those of \af{⊧-I-invar}.
\else
These facts are formalized in \agda as follows.

\begin{code}

module _ {X : Type χ}{𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝑆 α ρᵃ}{𝑩 : Algebra 𝑆 β ρᵇ}{p q : Term 𝑆 X} where
 open Hom

 ⊧-H-invar : 𝑨 ⊧ p ≈ q → 𝑩 IsHomImageOf 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-H-invar Apq (φh , φE) ρ =
  begin
       ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧(λ x → snd (φE (ρ x)))  ⟩
       ⟦ p ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)        ⟩
   φ(  ⟦ p ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   cong (homf φh) (Apq (φ⁻¹ ∘ ρ))         ⟩
   φ(  ⟦ q ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)        ⟩
       ⟦ q ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈⟨   cong ⟦ q ⟧(λ x → snd (φE (ρ x)))  ⟩
       ⟦ q ⟧   ⟨$⟩               ρ    ∎
  where
  φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
  φ⁻¹ = SurjInv (homf φh) φE
  private φ = (_⟨$⟩_ (homf φh))
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
  open Environment 𝑩  using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑩 ]

 ⊧-S-invar : 𝑨 ⊧ p ≈ q → 𝑩 ≤ 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-S-invar Apq B≤A b = isinj B≤A
  ( begin
    h (  ⟦ p ⟧   ⟨$⟩       b)  ≈⟨   comm-hom-term hh p b  ⟩
         ⟦ p ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈⟨   Apq (h ∘ b)           ⟩
         ⟦ q ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈˘⟨  comm-hom-term hh q b  ⟩
    h (  ⟦ q ⟧   ⟨$⟩       b)  ∎ )
  where
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩  using ( ⟦_⟧ )
  private hh = hom≤ B≤A ; h = _⟨$⟩_ (homf hh)

\end{code}
\fi
An identity satisfied by all algebras in an indexed collection is
also satisfied by the product of algebras in the collection.
\ifshort
We refer to this fact as \af{⊧-P-invar}.
\else

\begin{code}

module _ {X : Type χ}{𝑆 : Signature 𝓞 𝓥}{I : Type ℓ}(𝒜 : I → Algebra 𝑆 α ρᵃ){p q : Term 𝑆 X} where
 ⊧-P-invar : (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar 𝒜pq a =
  begin
   ⟦ p ⟧₁               ⟨$⟩  a                ≈⟨   interp-prod 𝒜 p a  ⟩
   ( λ i → (⟦ 𝒜 i ⟧ p)  ⟨$⟩  λ x → (a x) i )  ≈⟨ (λ i → 𝒜pq i (λ x → (a x) i)) ⟩
   ( λ i → (⟦ 𝒜 i ⟧ q)  ⟨$⟩  λ x → (a x) i )  ≈˘⟨  interp-prod 𝒜 q a  ⟩
   ⟦ q ⟧₁               ⟨$⟩  a                ∎
  where
  open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment        using ( ⟦_⟧ )
  open Setoid 𝔻[ ⨅ 𝒜 ]    using ( _≈_ )
  open SetoidReasoning 𝔻[ ⨅ 𝒜 ]

\end{code}
\fi

The classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦}, and \af V \ab{𝒦} all satisfy the
same term identities.  We will only use a subset of the inclusions needed to prove this
assertion, and we present here only the facts we need.\footnote{For more details, see the
\ualmodule{Varieties.Setoid.Preservation} module of the \agdaalgebras library.}
First, the closure operator \af H preserves the identities modeled by the
given class; this follows almost immediately from the invariance lemma
\af{⊧-H-invar} proved above.

\begin{AgdaAlign}
\begin{code}

module _  {X : Type χ}{𝑆 : Signature 𝓞 𝓥}{𝒦 : Pred(Algebra 𝑆 α ρᵃ) (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ lsuc ℓ)}{p q : Term 𝑆 X} where
 H-id1 : 𝒦 ⊫ p ≈ q → H{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 H-id1 σ 𝑩 (𝑨 , kA , BimgA) = ⊧-H-invar{p = p}{q} (σ 𝑨 kA) BimgA

\end{code}
The analogous preservation result for \af S is a simple consequence of
the invariance lemma \af{⊧-S-invar}; the obvious converse, which we call
\af{S-id2}, has an equally straightforward proof.

\begin{code}

 S-id1 : 𝒦 ⊫ p ≈ q → S{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A
 S-id2 : S ℓ 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))

\end{code}
Finally, we have analogous pairs of implications for \af P and \af V,
\ifshort
called P-id1 and V-id1 in the \agdaalgebras library.
\else
In each case, we will only need the first implication, so we omit the others from this presentation.

\begin{code}

 P-id1 : ∀{ι} → 𝒦 ⊫ p ≈ q → P{β = α}{ρᵃ}ℓ ι 𝒦 ⊫ p ≈ q
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
  where
  IH : ⨅ 𝒜 ⊧ p ≈ q
  IH = ⊧-P-invar 𝒜 {p}{q} (λ i → σ (𝒜 i) (kA i))

module _ {X : Type χ}{ι : Level}{𝑆 : Signature 𝓞 𝓥}(ℓ : Level){𝒦 : Pred(Algebra 𝑆 α ρᵃ) (α ⊔ ρᵃ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ)}
  {p q : Term 𝑆 X} where
 private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι

 V-id1 : 𝒦 ⊫ p ≈ q → V ℓ ι 𝒦 ⊫ p ≈ q
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
  H-id1 {ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA))
   where
   spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ} ℓ ι 𝒦)
   spA = ⨅A , (p⨅A , A≤⨅A)
   spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ p ≈ q
   spK⊧pq = S-id1 {ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)
\end{code}
\fi
\end{AgdaAlign}

%% -------------------------------------------------------------------------------------

\section{Free Algebras}
\label{free-algebras}
\paragraph*{The absolutely free algebra}
The term algebra \af{𝑻} \ab X is \emph{absolutely free} (or \emph{universal}, or
\emph{initial}) for algebras in the signature \ab{𝑆}. That is, for every
\ab{𝑆}-algebra \ab{𝑨}, the following hold.

\begin{itemize}
\item Every function from \ab{X} to \af{𝕌[ \ab{𝑨} ]} lifts to a homomorphism from \af{𝑻} \ab{X} to \ab{𝑨}.
\item The homomorphism that exists by the previous item is unique.
\end{itemize}

We now prove the first of these facts in \agda which we call \af{free-lift}.\footnote{\agdaalgebras also defines
 \af{free-lift-func} \as{:} \aof{𝔻[~\af{𝑻}~\ab X~]}~\aor{⟶}~\aof{𝔻[~\ab{𝑨}~]}
 for the analogous setoid function.}$^,$\footnote{For the proof of uniqueness,
see the \ualmodule{Terms.Setoid.Properties} module of the \agdaalgebras library.}

\begin{code}

module _ {X : Type χ}{𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝑆 α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 free-lift : 𝕌[ 𝑻 𝑆 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x) = h x
 free-lift (node f t) = (f ̂ 𝑨) (λ i → free-lift (t i))

\end{code}
\ifshort\else
\begin{code}
 free-lift-func : 𝔻[ 𝑻 𝑆 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong
  where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( reflexive to reflexiveᴬ )
  flcong : ∀ {s t} → s ≃ t → free-lift s ≈ free-lift t
  flcong (_≃_.rfl x) = reflexiveᴬ (≡.cong h x)
  flcong (_≃_.gnl x) = cong (Interp 𝑨) (≡.refl , (λ i → flcong (x i)))

\end{code}
\fi
Evidently, the proof is a straightforward structural induction argument.
\ifshort\else
At the base step, when the term has the form \aic{ℊ}
\ab x, the free lift of \ab h agrees with \ab h; at the inductive step, when the
term has the form \aic{node} \ab f \ab t, we assume (the induction hypothesis)
that the image of each subterm \ab t \ab i under the free lift of \ab h is known
and the free lift is defined by applying \ab f \aof{̂} \ab{𝑨} to these images.
\fi
Moreover, the free lift so defined is a homomorphism by construction;
\ifshort
for the proof---which is called \af{lift-hom} in the \agdaalgebras library---\seeshort.
\else
indeed, here is the trivial proof.

\begin{code}

 lift-hom : Hom (𝑻 𝑆 X) 𝑨
 lift-hom = hom free-lift-func hhom
  where
  hfunc : 𝔻[ 𝑻 𝑆 X ] ⟶ 𝔻[ 𝑨 ]
  hfunc = free-lift-func

  hcomp : compatible-map (𝑻 𝑆 X) 𝑨 free-lift-func
  hcomp {f}{a} = cong (Interp 𝑨) (≡.refl , (λ i → (cong free-lift-func){a i} ≃-isRefl))

  hhom : IsHom (𝑻 𝑆 X) 𝑨 hfunc
  hhom = mkhom (λ{f}{a} → hcomp{f}{a})

\end{code}
\fi

It turns out that the interpretation of a term \ab p in an environment \ab{η} is the same
as the free lift of \ab{η} evaluated at \ab p.

\ifshort\else
\begin{code}

module _ {X : Type χ}{𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝑆 α ρᵃ} where
 open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; refl )
 open Environment 𝑨  using ( ⟦_⟧ )
\end{code}
\fi
\begin{code}

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term 𝑆 X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x)       = refl
 free-lift-interp η (node f t)  = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)
\end{code}

\paragraph*{The relatively free algebra in theory}
In this subsection, we describe, for a given class \ab{𝒦} of \ab{𝑆}-algebras, the
\emph{relatively free algebra} in \af{S} (\af{P} \ab{𝒦}) over \ab X, using the informal
language that is typical of mathematics literature. In the next section we will present
the relatively free algebra in \agda using the formal language of type theory.

Above we defined the term algebra \T{X}, which is free in the class of all
\ab{𝑆}-algebras; that is, \T{X} has the universal property and belongs to the class of
\ab{𝑆}-algebras.  Given an arbitrary class \ab{𝒦} of \ab{𝑆}-algebras, we can't expect that
\T{X} belongs to \ab{𝒦}, so, in general, we say that \T{X} is free \emph{for} \ab{𝒦}.
\ifshort\else
Indeed, it might not be possible to find a free algebra that belongs to \ab{𝒦}.
\fi
However, for any class \ab{𝒦} we can construct an algebra that is free for \ab{𝒦}
and belongs to the class \af{S} (\af{P} \ab{𝒦}), and for most applications this suffices.

The informal construction of the free algebra in \af{S} (\af{P} \ab{𝒦}), for an arbitrary
class \ab{𝒦} of \ab{𝑆}-algebras, proceeds by taking the quotient of \T{X} modulo a congruence relation
that we will denote by \afld{≈}.  One approach is to let
\afld{≈} be \af{⋂}\{\ab{θ} \af{∈} \af{Con} (\T{X}) : \T{X} \af{/} \ab{θ} \af{∈} \af{S}
\ab{𝒦}\}.\footnote{\af{Con} (\T{X}) is the set of congruences of \T{X}.}
Equivalently, we let \ab{ℰ} = \af{Th} \ab{𝒦} and take \afld{≈} to be the least equivalence relation
on the domain of \T{X} such that
\begin{enumerate}
\item for every equation (\ab p , \ab q) \af{∈} \af{Th} \ab{𝒦} and every
environment \ab{ρ} : \ab X \as{→} \Term{X}, we have\\
\af{⟦~\ab p~⟧} \afld{⟨\$⟩} \ab{ρ} \afld{≈} \af{⟦~\ab q~⟧} \afld{⟨\$⟩} \ab{ρ}, and
\item \afld{≈} is a congruence of \T{X}; that is, for every operation symbol \ab
f : \af{∣~\ab{𝑆}~∣}, and for all tuples \ab{s} \ab{t} : \af{∥~\ab{𝑆}~∥} \ab f
→ \Term{X}, the following implication holds:\footnote{Here all
interpretations, denoted by \af{⟦\au{}⟧}, are with respect to \T{X}.}\\[-8pt]

(∀ i → \af{⟦~\ab{s}~\ab i~⟧}~\afld{⟨\$⟩}~\ab{ρ}~\afld{≈}~\af{⟦~\ab{t}~\ab
i~⟧}~\afld{⟨\$⟩}~\ab{ρ})
\as{→} \af{⟦~\ab f~\ab s~⟧}~\afld{⟨\$⟩}~\ab{ρ}~\afld{≈}~\af{⟦~\ab f~\ab
t~⟧}~\afld{⟨\$⟩}~\ab{ρ}\\[-8pt]
\end{enumerate}
The \defn{relatively free algebra over} \ab{X} (relative to
\ab{𝒦}) is defined to be the quotient \Free{X} := \T{X}~\af{/}~\afld{≈}.
Evidently \Free{X} is a subdirect product of the algebras in \{\T{X}~\af{/}~\ab{θ}\!\},
where \ab{θ} ranges over congruences modulo which \T{X} belongs to \af{S}~\ab{𝒦}.
Thus, \Free{X} \af{∈} \af{P}(\af{S}~\ab{𝒦}) ⊆ \af{S}(\af{P}~\ab{𝒦}), and it follows
that \Free{X} satisfies the identities in \af{Th} \ab{𝒦} (those modeled by all members of
\ab{𝒦}).  Indeed, for each pair \ab p \ab q : \Term{X}, if \ab{𝒦} \af{⊫} \ab p \af{≈} \ab
q, then \ab p and \ab q must belong to the same \afld{≈}-class, so \ab p and \ab q are
identified in \Free{X}. \ifshort\else (Notice that \afld{≈} may be empty, in which case
\T{X}~\af{/}~\afld{≈} is trivial.) \fi

\paragraph*{The relatively free algebra in \agda}
We now define the relatively free algebra in \agda using the language of type theory.
%Our approach looks a bit different from the informal one described above, because we
%represent quotients as setoids, but the end result is the same.
We start with a type \ab{ℰ} representing a collection of identities and, instead of
forming a quotient, we take the domain of the free algebra to be a setoid whose
\afld{Carrier} is the type \Term{X} of {𝑆}-terms in \ab X and whose equivalence relation
includes all pairs (\ab p , \ab q) \af{∈} \Term{X} \af{×} \Term{X} such that \ab p \aod{≈}
\ab q is derivable from \ab{ℰ}; that is, \ab{ℰ} \aod{⊢} \ab X \aod{▹} \ab p \aod{≈} \ab q.
Observe that elements of this setoid are equal iff they belong to the same equivalence
class of the congruence \afld{≈} defined above.  Therefore, the setoid so defined, which
we denote by \Free{X}, represents the quotient \T{X}~\af{/}~\afld{≈}.
Finally, the interpretation of an operation in the free algebra is simply the operation
itself, which works since \ab{ℰ} \aod{⊢} \ab X \aod{▹\au{}≈\au{}} is a congruence relation.

\begin{code}

module FreeAlgebra {𝑆 : Signature 𝓞 𝓥} (ℰ : {Y : Type χ} → Pred (Term 𝑆 Y × Term 𝑆 Y) (𝓞 ⊔ 𝓥 ⊔ lsuc χ)) where

 FreeDomain : Type χ → Setoid _ _
 FreeDomain X =
  record  { Carrier        = Term 𝑆 X
          ; _≈_            = ℰ ⊢ X ▹_≈_
          ; isEquivalence  = record { refl = reflexive ; sym = symmetric ; trans = transitive } }

 𝔽[_] : Type χ → Algebra 𝑆 (𝓞 ⊔ 𝓥 ⊔ lsuc χ) _
 Domain 𝔽[ X ] = FreeDomain X
 Interp 𝔽[ X ] = FreeInterp where
  FreeInterp : ∀ {X} → ⟨ 𝑆 ⟩ (FreeDomain X) ⟶ FreeDomain X
  FreeInterp ⟨$⟩ (f , ts)       = node f ts
  cong FreeInterp (≡.refl , h)  = app h
\end{code}

\paragraph*{The natural epimorphism} % from 𝑻 X to 𝔽[ X ]}
We now define the natural epimorphism from \T{X} onto \Free{X} %(= \T{X}~\af{/}~\afld{≈})
and prove that its kernel is contained in the collection of identities modeled by \af{V} \ab{𝒦}. % (which we represent by \af{Th} (\af{V} \ab{𝒦})).

\ifshort\else
\begin{code}

module FreeHom {𝑆 : Signature 𝓞 𝓥} {𝒦 : Pred(Algebra 𝑆 α ρᵃ) (α ⊔ ρᵃ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) } where
 private c = α ⊔ ρᵃ ⊔ ℓ
 open FreeAlgebra {χ = c} (Th 𝒦) using ( 𝔽[_] )
\end{code}
\fi
\begin{code}

 epiF[_] : (X : Type c) → Epi (𝑻 𝑆 X) 𝔽[ X ]
 epiF[ X ] = epi h hepi
  where
  open Setoid 𝔻[ 𝑻 𝑆 X ]     using ()        renaming ( _≈_ to _≈₀_  ; refl to reflᵀ )
  open Setoid 𝔻[ 𝔽[ X ] ]  using ( refl )  renaming ( _≈_ to _≈₁_  )
  open IsEpi ; open IsHom

  con : ∀ {x y} → x ≈₀ y → x ≈₁ y
  con (rfl {x}{y} ≡.refl) = refl
  con (gnl {f}{s}{t} x) = cong (Interp 𝔽[ X ]) (≡.refl , con ∘ x)

  h : 𝔻[ 𝑻 𝑆 X ] ⟶ 𝔻[ 𝔽[ X ] ]
  h = record { f = id ; cong = con }

  hepi : IsEpi (𝑻 𝑆 X) 𝔽[ X ] h
  hepi .isHom .compatible = cong h reflᵀ
  hepi .isSurjective y = y , refl

 homF[_] : (X : Type c) → Hom (𝑻 𝑆 X) 𝔽[ X ]
 homF[ X ] = IsEpi.HomReduct (Epi.isEpi epiF[ X ])

 kernel-in-theory : {X : Type c} → ker (Hom.homf homF[ X ]) ⊆ Th (V ℓ (𝓞 ⊔ 𝓥 ⊔ lsuc c) 𝒦)
 kernel-in-theory {X = X} {p , q} pKq 𝑨 vkA = V-id1 ℓ {p = p}{q} (ζ pKq) 𝑨 vkA
  where
  ζ : ∀{p q} → (Th 𝒦) ⊢ X ▹ p ≈ q → 𝒦 ⊫ p ≈ q
  ζ x 𝑨 kA = sound (λ y ρ → y 𝑨 kA ρ) x where open Soundness (Th 𝒦) 𝑨

\end{code}
Next we prove an important property of the relatively free algebra (relative to \ab{𝒦} and satisfying the identities in \af{Th} \ab{𝒦}), which will be used in the formalization of the HSP theorem; this is the assertion that for every algebra 𝑨, if \ab{𝑨} \af{⊨} \ab{Th} (\af{V} \ab{𝒦}), then there exists an epimorphism from \Free{A} onto \ab{𝑨}.

\ifshort\else
It is important to note that the \ab{Algebra} here is at a very different level than usual. Looks like
things have been stuffed into it that are non-standard.
\begin{code}

module _  {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra 𝑆 (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)} {𝒦 : Pred (Algebra 𝑆 α ρᵃ) (α ⊔ ρᵃ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) } where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = 𝓞 ⊔ 𝓥 ⊔ lsuc c
 open FreeHom {ℓ = ℓ} {_} {𝒦}
 open FreeAlgebra {χ = c}(Th 𝒦)  using ( 𝔽[_] )
 open Setoid 𝔻[ 𝑨 ]              using ( refl ; sym ; trans ) renaming  ( Carrier  to A )
\end{code}
\fi
\begin{code}

 F-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → Epi 𝔽[ A ] 𝑨
 F-ModTh-epi A∈ModThK = epi φ isEpi
  where
  open Hom ; open IsHom ; open IsEpi
  φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
  _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
  cong φ {p} {q} pq  =  trans  ( sym (free-lift-interp{𝑨 = 𝑨} id p) )
                     (  trans  ( A∈ModThK{p = p}{q} (kernel-in-theory pq) id )
                               ( free-lift-interp{𝑨 = 𝑨} id q ) )
  isEpi : IsEpi 𝔽[ A ] 𝑨 φ
  compatible (isHom isEpi) = cong (Interp 𝑨) (≡.refl , (λ _ → refl))
  isSurjective isEpi = λ y → ℊ y , refl
\end{code}
\ifshort\else

\medskip

\noindent Actually, we will need the following lifted version of this result.

\begin{code}

 F-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → Epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 F-ModTh-epi-lift A∈ModThK = ∘-epi (F-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi
\end{code}
\fi


%% -------------------------------------------------------------------------------------

\section{Birkhoff's Variety Theorem}

Birkhoff's variety theorem, also known as the HSP theorem, asserts that a class of algebras
is a variety if and only if it is an equational class.  In this section, we present the
statement and proof of the HSP theorem---first in the familiar, informal style similar to
what one finds in standard textbooks (see, e.g.,~\cite[Theorem 4.41]{Bergman:2012}),
and then in the formal language of Martin-Löf type theory using \agda.

\subsection{Informal proof}
Let \ab{𝒦} be a class of algebras and recall that \ab{𝒦} is a \emph{variety} provided
\ifshort\else
it is closed under homomorphisms, subalgebras and products; equivalently,
\fi
\af{V} \ab{𝒦} ⊆ \ab{𝒦}.\footnote{Recall, \af{V} \ab{𝒦} := \af{H} (\af{S} (\af{P} \ab{𝒦})),
and observe that \ab{𝒦} ⊆ \af{V} \ab{𝒦} holds for all \ab{𝒦} since
\af{V} is a closure operator.}
We call \ab{𝒦} an \emph{equational class} if it is precisely the class of all models of some set of identities.

It is easy to prove that \emph{every equational class is a variety}.  Indeed, suppose \ab{𝒦} is an equational
class axiomatized by the set \ab{ℰ} of term identities; that is, \ab{𝑨} ∈ \ab{𝒦} iff
\ab{𝑨} \af{⊨} \ab{ℰ}. Since the classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦} and
\ab{𝒦} all satisfy the same set of equations, we have \af{V} \ab{𝒦} \af{⊫} \ab p
\af{≈} \ab q for all (\ab p , \ab q) \af{∈} \ab{ℰ}, so \af{V} \ab{𝒦} ⊆ \ab{𝒦}.

The converse assertion---that \emph{every variety is an equational class}---is less obvious.
Let \ab{𝒦} be an arbitrary variety.  We will describe a set of equations that axiomatizes
\ab{𝒦}.  A natural choice is \af{Th} \ab{𝒦}, all equations that hold in \ab{𝒦}.
Let \ab{𝒦⁺} := \af{Mod} (\af{Th} \ab{𝒦}). Clearly, then \ab{𝒦} \aof{⊆} \ab{𝒦⁺}.  We prove the
reverse inclusion. Let \ab{𝑨} \af{∈} \ab{𝒦⁺}; it suffices to find an algebra \ab{𝑭} \af{∈}
\af{S} (\af{P} \ab{𝒦}) such that \ab{𝑨} is a homomorphic image of \ab{𝑭}, as this will
show that \ab{𝑨} \af{∈} \af{H} (\af{S} (\af{P} \ab{𝒦})) = \ab{𝒦}.

Let \ab{X} be such that there exists a \emph{surjective} environment
\ab{ρ} : \ab{X} \as{→} \af{𝕌[~\ab{𝑨}~]}.
%\footnote{This is usually done by assuming \ab{X} has cardinality at least max(|~\af{𝕌[~\ab{𝑨}~]}~|, ω).}
By the \af{lift-hom} lemma, there is an epimorphism \ab{h} from \T{X} onto \af{𝕌[~\ab{𝑨}~]}
that extends \ab{ρ}.
Now, put \aof{𝔽[~\ab{X}~]}~:=~\T{X}/\afld{≈}, and let \ab{g} : \T{X} \as{→} \aof{𝔽[~\ab{X}~]}
be the natural epimorphism with kernel \afld{≈}. We claim that \af{ker} \ab g \af{⊆}
\af{ker} \ab h. If the claim is true, then there is a map \ab{f} : \aof{𝔽[~\ab{X}~]} \as{→} \ab{𝑨}
such that \ab f \af{∘} \ab g = \ab h. Since \ab h is surjective, so is \ab f. Hence \ab{𝑨}
\af{∈} \af{𝖧} (\af{𝔽} \ab X) \aof{⊆} \ab{𝒦⁺} completing the proof.
To prove the claim, let \ab u , \ab v \af{∈} \T{X} and assume that \ab g \ab u =
\ab g \ab v. Since \T{X} is generated by \ab X, there are terms \ab p, \ab q ∈
\T{X} such that \ab u = \af{⟦~\T{X}~⟧} \ab p and v = \af{⟦~\T{X}~⟧} \ab
q.\footnote{Recall, \af{⟦~\ab{𝑨}~⟧} \ab t denotes the interpretation of the term
\ab t in the algebra \ab{𝑨}.} Therefore,\\[-4pt]

\af{⟦~\Free{X}~⟧} \ab p = \ab g (\af{⟦~\T{X}~⟧} \ab p) = \ab g \ab u = \ab g \ab v =
\ab g (\af{⟦~\T{X}~⟧} \ab q) = \af{⟦~\Free{X}~⟧} \ab q,\\[8pt]
so \ab{𝒦} \af{⊫} \ab p \af{≈} \ab q, so (\ab p , \ab q) \af{∈} \af{Th}
\ab{𝒦}. Since \ab{𝑨} \af{∈} \ab{𝒦⁺} =
\af{Mod} (\af{Th} \ab{𝒦}), we obtain \ab{𝑨} \af{⊧} \ab p \af{≈} \ab q, so \ab h
\ab u = (\af{⟦~\ab{𝑨}~⟧} \ab p) \aofld{⟨\$⟩} \ab{ρ} = (\af{⟦~\ab{𝑨}~⟧} \ab q)
\aofld{⟨\$⟩} \ab{ρ} = \ab h \ab v, as desired.

\subsection{Formal proof}
We now show how to formally express and prove the twin assertions that
(i) every equational class is a variety and (ii) every variety is an equational class.

\paragraph*{Every equational class is a variety}
For (i), we need an arbitrary equational class, which we obtain by starting with an arbitrary
collection \ab{ℰ} of equations and then defining \ab{𝒦} = \af{Mod} \ab{ℰ}, the equational class
determined by \ab{ℰ}. We prove that \ab{𝒦} is a variety by showing that
\ab{𝒦} = \af{V} \ab{𝒦}. The inclusion \ab{𝒦} \aof{⊆} \af V \ab{𝒦}, which holds for all
classes \ab{𝒦}, is called the \defn{expansive} property of \af{V}.

\ifshort\else
\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} (𝒦 : Pred(Algebra 𝑆 α ρᵃ) (α ⊔ ρᵃ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ)) where
\end{code}
\fi
\begin{code}

 V-expa : 𝒦 ⊆ V ℓ α 𝒦
 V-expa {x = 𝑨} kA = 𝑨 ,(𝑨 ,(⊤ ,(λ _ → 𝑨), (λ _ → kA), Goal), ≤-reflexive), IdHomImage
  where
  open Setoid 𝔻[ 𝑨 ] using ( refl )
  open Setoid 𝔻[ ⨅ (λ _ → 𝑨) ] using () renaming ( refl to refl⨅ )

  to⨅ : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ (λ _ → 𝑨) ]
  (to⨅ ⟨$⟩ x) = λ _ → x
  cong to⨅ xy = λ _ → xy

  from⨅ : 𝔻[ ⨅ (λ _ → 𝑨) ] ⟶ 𝔻[ 𝑨 ]
  (from⨅ ⟨$⟩ x) = x tt
  cong from⨅ xy = xy tt

  Goal : 𝑨 ≅ ⨅ (λ x → 𝑨)
  Goal = mkiso (hom to⨅ (mkhom refl⨅)) (hom from⨅ (mkhom refl)) (λ _ _ → refl) (λ _ → refl)

\end{code}

The converse inclusion, \af V \ab{𝒦} \aof{⊆} \ab{𝒦}, requires the
hypothesis that \ab{𝒦} is an equation class. Recall lemma
\af{V-id1}, which asserts that \ab{𝒦} \aof{⊫} \ab p \aof{≈} \ab q implies \af{V}
\ab{ℓ} \ab{ι} \ab{𝒦} \aof{⊫} \ab p \aof{≈} \ab q. Whence, if \ab{𝒦} is an equational
class, then \af V \ab{𝒦} \aof{⊆} \ab{𝒦}, as we now confirm.

\begin{code}

module _ {ℓ : Level}{X : Type ℓ}{𝑆 : Signature 𝓞 𝓥}{ℰ : {Y : Type ℓ} → Pred (Term 𝑆 Y × Term 𝑆 Y) (𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) } where
 private 𝒦 = Mod {α = ℓ} {ℓ} {X = X} ℰ     -- an arbitrary equational class
 EqCl⇒Var : V ℓ (𝓞 ⊔ 𝓥 ⊔ lsuc ℓ) 𝒦 ⊆ 𝒦
 EqCl⇒Var {𝑨}vA{p}{q} pℰq ρ = V-id1 ℓ {𝒦}{p}{q}(λ _ x τ → x pℰq τ)𝑨 vA ρ

\end{code}
Together, \af{V-expa} and \af{Eqcl⇒Var} prove that every equational class is a variety.


\paragraph*{Every variety is an equational class}
For (ii), we need an arbitrary variety, which we obtain by starting with an arbitrary class
\ab{𝒦} of \ab{𝑆}-algebras and taking the \emph{varietal closure}, \af{V} \ab{𝒦}.
We prove that \af{V} \ab{𝒦} is an equational class by showing it is precisely the collection of
algebras that model the equations in \af{Th} (\af{V} \ab{𝒦}); that is, we prove
\af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})).
The inclusion \af{V} \ab{𝒦} \aof{⊆} \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) is a simple
consequence of the fact that \af{Mod} \af{Th} is a closure operator%
\ifshort
, so we omit the proof and later refer to this fact as \af{ModTh-closure}.
\else
. Nonetheless, completeness demands that we formalize this fact, however trivial its proof.

\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥}(𝒦 : Pred(Algebra 𝑆 α ρᵃ) (α ⊔ ρᵃ ⊔ 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = 𝓞 ⊔ 𝓥 ⊔ lsuc c

 ModTh-closure : V{β = β}{ρᵇ}{γ}{ρᶜ}{δ}{ρᵈ} ℓ ι 𝒦 ⊆ Mod{X = X} (Th (V ℓ ι 𝒦))
 ModTh-closure {x = 𝑨} vA {p}{q} x ρ = x 𝑨 vA ρ

\end{code}
\fi

It remains to prove the inclusion \af{Mod} (\af{Th} (V 𝒦)) \aof{⊆} \af{V} \ab{𝒦},
and this task occupies the remainder of the paper.  We proceed as follows:

\begin{enumerate}
\item \label{item:1} Let \ab{𝑪} be the product of all algebras in \af{S} \ab{𝒦}, so that \ab{𝑪} \af{∈} \af{P} (\af{S} \ab{𝒦}).
\item Prove \af{P} (\af{S} \ab{𝒦}) \af{⊆} \af{S} (\af{P} \ab{𝒦}), so \ab{𝑪} \af{∈} \af{S} (\af{P} \ab{𝒦}) by item~\ref{item:1}.
\item Prove \aof{𝔽[ \ab{X} ]} \af{≤} \ab{𝑪}, so that \aof{𝔽[ \ab{X} ]} \af{∈} \af{S} (\af{S} (\af{P} \ab{𝒦})) (= \af{S} (\af{P} \ab{𝒦})).
\item Prove that every algebra in \af{Mod} (\af{Th} (V 𝒦)) is a homomorphic image of
\aof{𝔽[ \ab{X} ]} and thus belongs to \af{H} (\af{S} (\af{P} \ab{𝒦})) (= \af{V} \ab{𝒦}).
\end{enumerate}

To define \ab{𝑪} as the product of all algebras in \af{S} \ab{𝒦}, we must first contrive
an index type for the class \af{S} \ab{𝒦}.  We do so by letting the indices be the algebras
belonging to \ab{𝒦}. Actually, each index will consist of a triple (\ab{𝑨} , \ab p ,
\ab{ρ}) where \ab{𝑨} is an algebra, \ab p : \ab{𝑨} \af{∈} \af{S} \ab{𝒦} is a proof of membership in \ab{𝒦},
and \ab{ρ} : \ab X \as{→} \aof{𝕌[ \ab{𝑨} ]} is an arbitrary environment.
Using this indexing scheme, we construct \ab{𝑪}, the product of all algebras in \ab{𝒦}
and all environments, as follows.

\ifshort\else
\begin{code}

 open FreeHom {ℓ = ℓ} {𝑆} {𝒦}
 open FreeAlgebra {χ = c} (Th 𝒦)  using ( 𝔽[_] )
 open Environment                  using ( Env )
\end{code}
\fi
\begin{code}

 ℑ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc α ⊔ lsuc ρᵃ ⊔ lsuc ℓ)
 ℑ = Σ[ 𝑨 ∈ (Algebra 𝑆 α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) × (Carrier (Env 𝑨 X))

 𝔄 : ℑ → Algebra 𝑆 α ρᵃ
 𝔄 i = ∣ i ∣

 𝑪 : Algebra 𝑆 (α ⊔ (𝓞 ⊔ 𝓥 ⊔ lsuc α ⊔ lsuc ρᵃ ⊔ lsuc ℓ)) (𝓞 ⊔ 𝓥 ⊔ lsuc α ⊔ lsuc ρᵃ ⊔ lsuc ℓ)
 𝑪 = ⨅ 𝔄
\end{code}

\ifshort\else
\begin{code}

 skEqual : (i : ℑ) → ∀{p q} → Type ρᵃ
 skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
  where open Setoid 𝔻[ 𝔄 i ] using ( _≈_ ) ; open Environment (𝔄 i) using ( ⟦_⟧ )

\end{code}
The type \af{skEqual} provides a term identity \ab p \af{≈} \ab q for each index \ab i = (\ab{𝑨} , \ab{p} , \ab{ρ}) of the product.
%(here, as above, \ab{𝑨} is an algebra, \ab{sA} is a proof that \ab{𝑨} belongs to \af{S} \ab{𝒦}, and \ab{ρ} is an environment).
%map assigning values in the domain of \ab{𝑨} to variable symbols in \ab X).
Later we prove that if the identity \ab{p} \af{≈} \ab q holds in all \ab{𝑨} \aof{∈} \af S \ab{𝒦} (for all environments), then \ab p \af{≈} \ab q
holds in the relatively free algebra \Free{X}; equivalently, the pair (\ab p , \ab q) belongs to the
kernel of the natural homomorphism from \T{X} onto \Free{X}. We will use that fact to prove
that the kernel of the natural hom from \T{X} to \ab{𝑪} is contained in the kernel of the natural hom from \T{X} onto \Free{X},
whence we construct a monomorphism from \Free{X} into \ab{𝑪}, and thus \Free{X} is a subalgebra of \ab{𝑪},
so belongs to \af S (\af P \ab{𝒦}).
\fi

\begin{code}

 homC : Hom (𝑻 𝑆 X) 𝑪
 homC = ⨅-hom-co 𝔄 (λ i → lift-hom (snd ∥ i ∥))
\end{code}
\ifshort\else
\begin{code}

 kerF⊆kerC : ker (Hom.homf homF[ X ]) ⊆ ker (Hom.homf homC)
 kerF⊆kerC {p , q} pKq (𝑨 , sA , ρ) = Goal
  where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; sym ; trans )
  open Environment 𝑨  using ( ⟦_⟧ )
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ free-lift ρ t
  fl t = free-lift-interp {𝑨 = 𝑨} ρ t

  ζ : ∀{p q} → (Th 𝒦) ⊢ X ▹ p ≈ q → 𝒦 ⊫ p ≈ q
  ζ x 𝑨 kA = sound (λ y ρ → y 𝑨 kA ρ) x where open Soundness (Th 𝒦) 𝑨

  subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  subgoal = S-id1{ℓ = ℓ}{p = p}{q} (ζ pKq) 𝑨 sA ρ
  Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ (free-lift{𝑨 = 𝑨} ρ q)
  Goal = trans (sym (fl p)) (trans subgoal (fl q))
\end{code}
\fi
\begin{code}

 homFC : Hom 𝔽[ X ] 𝑪
 homFC = ∣ HomFactor 𝑪 homC homF[ X ] kerF⊆kerC (IsEpi.isSurjective (Epi.isEpi (epiF[ X ]))) ∣

\end{code}
If \AgdaPair{p}{q} belongs to the kernel of \af{homC}, then
\af{Th} \ab{𝒦} includes the identity \ab{p} \af{≈} \ab{q}.
%---that is, \af{Th} \ab{𝒦} \af{⊢} \ab X \af{▹} \ab{p} \af{≈} \ab{q}.
Equivalently,
the kernel of \af{homC} is contained in that of \af{homF[ X ]}.
\ifshort
We omit the proof of this lemma and merely display its formal statement.
\else
\fi

\begin{code}

 kerC⊆kerF : ∀{p q} → (p , q) ∈ ker (Hom.homf homC) → (p , q) ∈ ker (Hom.homf homF[ X ])
\end{code}
\ifshort
\vskip2mm
\else
\begin{code}
 kerC⊆kerF {p}{q} pKq = S𝒦⊫→ker𝔽 (S𝒦⊫ pqEqual)
  where
  S𝒦⊫ : (∀ i → skEqual i {p}{q}) → S{β = α}{ρᵃ} ℓ 𝒦 ⊫ p ≈ q
  S𝒦⊫ x 𝑨 sA ρ = x (𝑨 , sA , ρ)
  S𝒦⊫→ker𝔽 : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ p ≈ q → (p , q) ∈ ker (Hom.homf homF[ X ])
  S𝒦⊫→ker𝔽 x = hyp (S-id2{ℓ = ℓ}{p = p}{q} x)

  pqEqual : ∀ i → skEqual i {p}{q}
  pqEqual i = goal
   where
   open Environment (𝔄 i)  using ( ⟦_⟧ )
   open Setoid 𝔻[ 𝔄 i ]    using ( _≈_ ; sym ; trans )
   goal : ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
   goal  = trans (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
         ( trans (pKq i)(sym (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))

\end{code}
\fi
\noindent We conclude that the homomorphism from \Free{X} to \af{𝑪} is injective, whence \Free{X} is (isomorphic to) a subalgebra of \af{𝑪}.

\begin{code}

 monFC : Mon 𝔽[ X ] 𝑪
 monFC = mon (Hom.homf homFC) isMon
  where
  open IsMon ; open IsHom
  isMon : IsMon 𝔽[ X ] 𝑪 (Hom.homf homFC)
  isMon = record { isHom = Hom.isHom homFC
                 ; isInjective = kerC⊆kerF
                 }

 F≤C : 𝔽[ X ] ≤ 𝑪
 F≤C = mon→≤ monFC

\end{code}
Using the last result we prove that \Free{X} belongs to \af{S} (\af{P} \ab{𝒦}). This
requires one more technical lemma concerning the classes \af{S} and \af{P}; specifically,
\ifshort
\af{P} (\af{S} \ab{𝒦}) \aof{⊆} \af{S} (\af{P} \ab{𝒦}) holds for every class \ab{𝒦}.
The \agdaalgebras library contains the formal statement and proof of this result, where
it is called \af{PS⊆SP} (\seeshort).
\else
a product of subalgebras of algebras in a class is a subalgebra of a product of algebras in the class;
in other terms, \af{P} (\af{S} \ab{𝒦}) \aof{⊆} \af{S} (\af{P} \ab{𝒦}), for every class \ab{𝒦}.
We state and prove this in \agda as follows.

\begin{code}
 private 𝒶 = α ⊔ ρᵃ ; oaℓ = 𝓞 ⊔ 𝓥 ⊔ lsuc (𝒶 ⊔ ℓ)

 PS⊆SP : P (𝒶 ⊔ ℓ) oaℓ (S{β = α}{ρᵃ} ℓ 𝒦) ⊆ S oaℓ (P ℓ oaℓ 𝒦)
 PS⊆SP {𝑩} (I , ( 𝒜 , sA , B≅⨅A )) = Goal
  where
  ℬ : I → Algebra 𝑆 α ρᵃ
  ℬ i = ∣ sA i ∣
  kB : (i : I) → ℬ i ∈ 𝒦
  kB i =  fst ∥ sA i ∥
  ⨅A≤⨅B : ⨅ 𝒜 ≤ ⨅ ℬ
  ⨅A≤⨅B = ⨅-≤ λ i → snd ∥ sA i ∥
  Goal : 𝑩 ∈ S{β = oaℓ}{oaℓ}oaℓ (P {β = oaℓ}{oaℓ} ℓ oaℓ 𝒦)
  Goal = ⨅ ℬ , (I , (ℬ , (kB , ≅-refl))) , (≅-trans-≤ B≅⨅A ⨅A≤⨅B)

\end{code}
With this we can prove that \Free{X} belongs to \af{S} (\af{P} \ab{𝒦}).
\fi

\begin{code}

 SPF : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SPF = ∣ spC ∣ , (fst ∥ spC ∥) , (≤-transitive F≤C (snd ∥ spC ∥))
  where
  psC : 𝑪 ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
  psC = ℑ , (𝔄 , ((λ i → fst ∥ i ∥) , ≅-refl))
  spC : 𝑪 ∈ S ι (P ℓ ι 𝒦)
  spC = PS⊆SP psC

\end{code}
Finally, we prove that every algebra in \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) is a homomorphic image of \af{𝔽[~\ab{X}~]}.

\ifshort\else
\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} {𝒦 : Pred(Algebra 𝑆 α ρᵃ) (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ lsuc ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = 𝓞 ⊔ 𝓥 ⊔ lsuc c
 open FreeAlgebra {χ = c}(Th 𝒦) using ( 𝔽[_] )
 open Epi
\end{code}
\fi
\begin{code}
 Var⇒EqCl : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Var⇒EqCl 𝑨 ModThA = 𝔽[ 𝕌[ 𝑨 ] ] , (spFA , AimgF)
  where
  open Hom ; open IsEpi
  spFA : 𝔽[ 𝕌[ 𝑨 ] ] ∈ S{ι} ι (P ℓ ι 𝒦)
  spFA = SPF {ℓ = ℓ} 𝒦
  epiFlA : Epi 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 _ _)
  epiFlA = F-ModTh-epi-lift {ℓ = ℓ} (λ {p q} → ModThA{p = p}{q})
  φ : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  φ = hom (Epi.epif epiFlA) (isHom (isEpi epiFlA)) , isSurjective (isEpi epiFlA)
  AimgF : 𝑨 IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  AimgF = ∘-hom ∣ φ ∣ (from Lift-≅), λ y → (fst (∥ φ ∥ (homf (to (Lift-≅ {𝑨 = 𝑨}{_}{ρᵃ})) ⟨$⟩ y))) , reflˢ 𝔻[ 𝑨 ]

\end{code}
\af{ModTh-closure} and \af{Var⇒EqCl} show that
\af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) holds for every class \ab{𝒦} of \ab{𝑆}-algebras.
Thus, every variety is an equational class. This completes the formal proof of Birkhoff's variety theorem.

%% -----------------------------------------------------------------------------
\section{Related work}
There have been a number of efforts to formalize parts of universal algebra in
type theory besides ours.
In~\cite{Capretta:1999}, Capretta formalized the basics of universal algebra in the
   Calculus of Inductive Constructions using the Coq proof assistant.
In~\cite{Spitters:2011}, Spitters and van der Weegen formalized the basics of universal algebra
   and some classical algebraic structures, also in the Calculus of Inductive Constructions using
   the Coq proof assistant and promoting the use of type classes.
In~\cite{Gunther:2018} Gunther et al developed what seemed (prior to the \agdaalgebras library) to be
   the most extensive library of formalized universal algebra to date; like \agdaalgebras,
   that work is based on dependent type theory, is programmed in \agda, and goes beyond the
   Noether isomorphism theorems to include some basic equational logic; although the
   coverage is less extensive than that of \agdaalgebras, Gunther et al do treat
   \emph{multi-sorted} algebras, whereas \agdaalgebras is currently limited to single
   sorted structures.

As noted by Abel~\cite{Abel:2021}, Amato et al, in \cite{Amato:2021}, have
   formalized multi-sorted algebras with finitary operators in UniMath. The restriction to
   finitary operations was due to limitations of the UniMath type theory, which does
   not have W-types nor user-defined inductive types.
Abel also notes that Lynge and Spitters, in~\cite{Lynge:2019}, formalize multi-sorted
   algebras with finitary operators in \emph{Homotopy type theory} (\cite{HoTT}) using
   Coq.  HoTT's higher inductive types enable them to define quotients as types, without
   the need for setoids.  Lynge and Spitters prove three isomorphism theorems concerning
   subalgebras and quotient algebras, but do not formalize universal algebras nor varieties.
Finally, in~\cite{Abel:2021}, Abel gives a new formal proof of the soundness theorem and
   Birkhoff's completeness theorem for multi-sorted algebraic structures.

%Some other projects aimed at formalizing mathematics generally, and algebra in particular, have developed into very extensive libraries that include definitions, theorems, and proofs about algebraic structures, such as groups, rings, modules, etc.  However, the goals of these efforts seem to be the formalization of special classical algebraic structures, as opposed to the general theory of (universal) algebras. Moreover, the part of universal algebra and equational logic formalized in the \agdaalgebras library extends beyond the scope of prior efforts.

%Prior to our work, a constructive version of Birkhoff's theorem was published by Carlstr\"om in~\cite{Carlstrom:2008}.  However, the logical foundations of that work is constructive set theory and, as far as we know, there was no attempt to formalized it in type theory and verify it with a proof assistant.
