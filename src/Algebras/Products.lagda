<h2>Algebras.Products module</h2>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Algebras.Products {𝑆 : Signature 𝓞 𝓥} where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Agda.Primitive  using ( lsuc ; _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ ; Σ-syntax )
open import Level using ( Level )
open import Relation.Unary  using ( Pred ; _⊆_ ; _∈_ )

-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries using (_⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
open import Algebras.Basic using ( Algebra ; _̂_ ; algebra )

private variable α β ρ 𝓘 : Level

\end{code}

<h3>Products of Algebras and Product Algebras</h3>

Recall the informal definition of a <i>product</i> of `𝑆`-algebras. Given a type `I : Type 𝓘` and a family `𝒜 : I → Algebra α 𝑆`, the <i>product</i> `⨅ 𝒜` is the algebra whose domain is the Cartesian product `Π 𝑖 ꞉ I , ∣ 𝒜 𝑖 ∣` of the domains of the algebras in `𝒜`, and whose operations are defined as follows: if `𝑓` is a `J`-ary operation symbol and if `𝑎 : Π 𝑖 ꞉ I , J → 𝒜 𝑖` is an `I`-tuple of `J`-tuples such that `𝑎 𝑖` is a `J`-tuple of elements of `𝒜 𝑖` (for each `𝑖`), then `(𝑓 ̂ ⨅ 𝒜) 𝑎 := (i : I) → (𝑓 ̂ 𝒜 i)(𝑎 i)`.

In [UniversalAlgebra][] a <i>product of</i> `𝑆`-<i>algebras</i> is represented by the following type.

\begin{code}

⨅ : {I : Type 𝓘 }(𝒜 : I → Algebra α 𝑆 ) → Algebra (𝓘 ⊔ α) 𝑆

⨅ {I = I} 𝒜 = ( ∀ (i : I) → ∣ 𝒜 i ∣ ) ,           -- domain of the product algebra
               λ 𝑓 𝑎 i → (𝑓 ̂ 𝒜 i) λ x → 𝑎 x i   -- basic operations of the product algebra

\end{code}

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UniversalAlgebra][] library whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

\begin{code}

open algebra

⨅' : {I : Type 𝓘 }(𝒜 : I → algebra α 𝑆) → algebra (𝓘 ⊔ α) 𝑆

⨅' {I} 𝒜 = record { carrier = ∀ i → carrier (𝒜 i) ;                 -- domain
                     opsymbol = λ 𝑓 𝑎 i → (opsymbol (𝒜 i)) 𝑓 λ x → 𝑎 x i } -- basic operations

\end{code}


<b>Notation</b>. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra α 𝑆` has type `Type(𝓞 ⊔ 𝓥 ⊔ lsuc α)`.  Such types occur so often in the [UniversalAlgebra][] library that we define the following shorthand for their universes.

\begin{code}

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α

\end{code}


<h4 id="products-of-classes-of-algebras">Products of classes of algebras</h4>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra α 𝑆`, for some universe level `α` and signature `𝑆`. That is, `𝒦 : Pred (Algebra α 𝑆) β`, for some type `β`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is certainly not what we want.  For recall that `Pred (Algebra α 𝑆) β` is just an alias for the function type `Algebra α 𝑆 → Type β`, and the semantics of the latter takes `𝒦 𝑨` (and `𝑨 ∈ 𝒦`) to mean that `𝑨` belongs to the class `𝒦`. Thus, by definition,

```agda
 Π 𝒦   :=   Π 𝑨 ꞉ (Algebra α 𝑆) , 𝒦 𝑨   :=   ∀ (𝑨 : Algebra α 𝑆) → 𝑨 ∈ 𝒦,
```

which asserts that every inhabitant of the type `Algebra α 𝑆` belongs to `𝒦`.  Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra α 𝑆) → Type β`) and the type `Algebra α 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra α 𝑆` belonging to `𝒦`.

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.

\begin{code}

module _ {𝒦 : Pred (Algebra α 𝑆)(ov α)} where
 ℑ : Type (ov α)
 ℑ = Σ[ 𝑨 ∈ Algebra α 𝑆 ] 𝑨 ∈ 𝒦

\end{code}

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

\begin{code}

 𝔄 : ℑ → Algebra α 𝑆
 𝔄 i = ∣ i ∣

\end{code}

Finally, we define `class-product` which represents the product of all members of 𝒦.

\begin{code}

 class-product : Algebra (ov α) 𝑆
 class-product = ⨅ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an <i>index</i> over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.

--------------------------------------------

<br>
<br>

[← Algebras.Congruences](Algebras.Congruences.html)
<span style="float:right;">[Algebras.Setoid →](Algebras.Setoid.html)</span>

{% include UALib.Links.md %}

