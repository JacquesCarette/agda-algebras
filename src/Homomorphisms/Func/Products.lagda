---
layout: default
title : "Homomorphisms.Func.Products module (The Agda Universal Algebra Library)"
date : "2021-09-21"
author: "agda-algebras development team"
---

#### <a id="products-of-homomorphisms">Products of Homomorphisms of SetoidAlgebras</a>

This is the [Homomorphisms.Func.Products] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Func.Products {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------
open import Agda.Primitive   using ( _⊔_ ; lsuc ) renaming ( Set to Type )
open import Function.Bundles using ( Func )
open import Data.Product     using ( _,_ )
open import Level            using ( Level )
open import Relation.Binary using ( Setoid )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

-- Imports from the Agda Universal Algebras Library ----------------------
open import Overture.Preliminaries using ( ∣_∣ ; ∥_∥)
open import Overture.Func.Preliminaries using ( _⟶_ )
open import Algebras.Func.Basic       {𝑆 = 𝑆} using ( SetoidAlgebra )
open import Algebras.Func.Products    {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic  {𝑆 = 𝑆} using ( hom ; IsHom ; epi )

private variable
 α ρᵃ β ρᵇ 𝓘 : Level

\end{code}

Suppose we have an algebra `𝑨`, a type `I : Type 𝓘`, and a family `ℬ : I → Algebra β 𝑆` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `ℬ` an *indexed family of algebras*.

If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.

\begin{code}

module _ {I : Type 𝓘}{𝑨 : SetoidAlgebra α ρᵃ}(ℬ : I → SetoidAlgebra β ρᵇ)  where
 open SetoidAlgebra 𝑨 using () renaming ( Domain to A )
 open Setoid A using ( ) renaming ( refl to refl₁ )
 open SetoidAlgebra (⨅ ℬ) using () renaming ( Domain to ⨅B )
 open Func using ( cong ) renaming ( f to _⟨$⟩_ )
 open SetoidAlgebra using ( Domain )
 open Setoid using ( refl )
 open IsHom using (compatible ; preserves≈)
 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom
  where
  h : A ⟶ ⨅B
  _⟨$⟩_ h = λ a i → ∣ 𝒽 i ∣ ⟨$⟩ a
  cong h xy i = cong ∣ 𝒽 i ∣ xy
  hhom : IsHom 𝑨 (⨅ ℬ) h
  compatible hhom i = compatible ∥ 𝒽 i ∥
  preserves≈ hhom = cong h

\end{code}

The family `𝒽` of homomorphisms inhabits the dependent type `Π i ꞉ I , hom 𝑨 (ℬ i)`.  The syntax we use to represent this type is available to us because of the way `-Π` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`Π λ i → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `(i : I) → hom 𝑨 (ℬ i)` &nbsp; or &nbsp; `∀ i → hom 𝑨 (ℬ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `𝒜 : I → Algebra α 𝑆 and ℬ : I → Algebra β 𝑆` (two families of `𝑆`-algebras), and `𝒽 :  Π i ꞉ I , hom (𝒜 i)(ℬ i)` (a family of homomorphisms), then we can construct a homomorphism from `⨅ 𝒜` to `⨅ ℬ` in the following natural way.

\begin{code}

 -- ⨅-hom : (𝒜 : I → SetoidAlgebra α ρᵃ) → (∀ (i : I) → hom (𝒜 i) (ℬ i)) → hom (⨅ 𝒜)(⨅ ℬ)
 -- ⨅-hom 𝒜 𝒽 = {!!} -- (λ x i → ∣ 𝒽 i ∣ (x i)) , (λ 𝑓 𝒶 → λ i → ∥ 𝒽 i ∥ 𝑓 (λ x → 𝒶 x i))

\end{code}


#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.

\begin{code}

 -- ⨅-projection-hom : (i : I) → hom (⨅ ℬ) (ℬ i)
 -- ⨅-projection-hom = {!!} -- λ x → (λ z → z x) , λ _ _ → ≡.refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.

---------------------------------

<span style="float:left;">[← Homomorphisms.Kernels](Homomorphisms.Kernels.html)</span>
<span style="float:right;">[Homomorphisms.Noether →](Homomorphisms.Noether.html)</span>

{% include UALib.Links.md %}
