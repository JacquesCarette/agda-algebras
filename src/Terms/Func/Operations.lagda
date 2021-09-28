---
layout: default
title : "Terms.Operations module (The Agda Universal Algebra Library)"
date : "2021-09-25"
author: "agda-algebras development team"
---

#### <a id="term-operations">Term Operations for Setoid Algebras</a>

This section presents the [Terms.Func.Operations][] module of the [Agda Universal Algebra Library][].

Here we define *term operations* which are simply terms interpreted in a particular algebra, and we prove some compatibility properties of term operations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Terms.Func.Operations {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive   using ( Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ )
open import Function.Base    using ( _∘_ )
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )

-- Imports from Agda Universal Algebra Library ----------------------------------------------
open import Overture.Preliminaries           using ( ∣_∣ ; ∥_∥ )
open import Algebras.Func.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; _̂_ ; ov )
open import Algebras.Func.Products   {𝑆 = 𝑆} using ( ⨅ )
open import Homomorphisms.Func.Basic {𝑆 = 𝑆} using ( hom ; IsHom )
open import Terms.Basic              {𝑆 = 𝑆} using ( Term )
open import Terms.Func.Basic         {𝑆 = 𝑆} using ( module Environment ; 𝑻 ; _≐_ ; ≐-isRefl )
open import Terms.Func.Properties    {𝑆 = 𝑆} using ( free-lift )

open Term
open Func using ( cong ) renaming ( f to _⟨$⟩_ )

private variable
 α ρᵃ β ρᵇ ρ χ ι : Level
 X : Type χ

\end{code}

It turns out that the intepretation of a term is the same as the `free-lift` (modulo argument order and assuming function extensionality).

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ} where
 open SetoidAlgebra 𝑨 using ( Interp ) renaming (Domain to A )
 open Setoid A using ( _≈_ ; refl ) renaming ( Carrier to ∣A∣ )
 open Environment 𝑨 using ( ⟦_⟧ ) -- renaming ( ⟦_⟧ to ⟦_⟧₁ )

 free-lift-interp : (η : X → ∣A∣)(p : Term X)
  →                 ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p

 free-lift-interp η (ℊ x) = refl
 free-lift-interp η (node f t) = cong Interp (≡.refl , (free-lift-interp η) ∘ t)

module _ {X : Type χ} where
 open SetoidAlgebra (𝑻 X) using ( Interp ) renaming (Domain to TX )
 open Setoid TX using ( _≈_ ; refl ) renaming ( Carrier to ∣TX∣ )
 open Environment (𝑻 X) using ( ⟦_⟧ ; ≐→Equal )
 open SetoidReasoning TX

 term-interp : (f : ∣ 𝑆 ∣){s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → s i ≐ t i)
  →            ∀ η → ⟦ node f s ⟧ ⟨$⟩ η ≈ ⟦ node f t ⟧ ⟨$⟩ η -- (f ̂ 𝑻 X) t
 term-interp f {s}{t} st η = cong Interp (≡.refl , λ i → ≐→Equal (s i) (t i) (st i) η )

 term-agreement : (p : Term X) → p ≈ ⟦ p ⟧ ⟨$⟩ ℊ
 term-agreement (ℊ x) = refl
 term-agreement (node f t) = cong Interp (≡.refl , (λ i → term-agreement (t i)))

\end{code}



#### <a id="interpretation-of-terms-in-product-algebras">Interpretation of terms in product algebras</a>

\begin{code}

module _ {X : Type χ }{I : Type ι}
         (𝒜 : I → SetoidAlgebra α ρᵃ) where
 open SetoidAlgebra (⨅ 𝒜) using (Interp) renaming ( Domain to ⨅A )
 open Setoid ⨅A using ( _≈_ ; refl )
 open Environment (⨅ 𝒜) using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment using ( ⟦_⟧ ; ≐→Equal )

 interp-prod : (p : Term X)
  →            ∀ ρ → ⟦ p ⟧₁ ⟨$⟩ ρ ≈ (λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ (λ x → (ρ x) i))
 interp-prod (ℊ x) = λ ρ i → ≐→Equal (𝒜 i) (ℊ x) (ℊ x) ≐-isRefl λ x' → (ρ x) i
 interp-prod (node f t) = λ ρ i → cong Interp (≡.refl , (λ j k → interp-prod (t j) ρ k)) i
 
\end{code}


#### <a id="compatibility-of-terms">Compatibility of terms</a>

We now prove two important facts about term operations.  The first of these, which is used very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open SetoidAlgebra 𝑨 using () renaming (Domain to A ; Interp to Interp₁ )
 open Setoid A using () renaming ( _≈_ to _≈₁_ ; Carrier to ∣A∣ )

 open SetoidAlgebra 𝑩 using () renaming (Domain to B ; Interp to Interp₂ )
 open Setoid B using ( _≈_ ; sym ; refl )

 open SetoidReasoning B

 private
  hfunc = ∣ hh ∣
  h = _⟨$⟩_ hfunc

 open Environment 𝑨 using ( ) renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment 𝑩 using ( ) renaming ( ⟦_⟧ to ⟦_⟧₂ )
 open IsHom
 comm-hom-term : (t : Term X) (a : X → ∣A∣)
                -----------------------------------------
  →             h (⟦ t ⟧₁ ⟨$⟩ a) ≈ ⟦ t ⟧₂ ⟨$⟩ (h ∘ a)

 comm-hom-term (ℊ x) a = refl
 comm-hom-term (node f t) a = goal
  where
  goal : h (⟦ node f t ⟧₁ ⟨$⟩ a) ≈ (⟦ node f t ⟧₂ ⟨$⟩ (h ∘ a))
  goal =
   begin
    h (⟦ node f t ⟧₁ ⟨$⟩ a)             ≈⟨ (compatible ∥ hh ∥) ⟩
    (f ̂ 𝑩)(λ i → h (⟦ t i ⟧₁ ⟨$⟩ a))   ≈⟨ cong Interp₂ (≡.refl , λ i → comm-hom-term (t i) a) ⟩
    (f ̂ 𝑩)(λ i → ⟦ t i ⟧₂ ⟨$⟩ (h ∘ a)) ≈⟨ refl ⟩
    (⟦ node f t ⟧₂ ⟨$⟩ (h ∘ a))
   ∎

\end{code}


#### <a id="substitution">Substitution</a>

A substitution from `Y` to `X` is simply a function from `Y` to `X`, and the application of a substitution is represented as follows.

\begin{code}

_[_] : {χ : Level}{X Y : Type χ} → Term Y → (Y → X) → Term X
(ℊ y) [ σ ] = ℊ (σ y)
(node f t)  [ σ ] = node f λ i → t i [ σ ]

\end{code}

Alternatively, we may want a substitution that replaces each variable symbol in `Y`, not with an element of `X`, but with a term from `Term X`.

\begin{code}

-- Substerm X Y, an inhabitant of which replaces each variable symbol in Y with a term from Term X.
Substerm : (X Y : Type χ) → Type (ov χ)
Substerm X Y = (y : Y) → Term X

-- Application of a Substerm.
_[_]t : {X Y : Type χ } → Term Y → Substerm X Y → Term X
(ℊ y) [ σ ]t = σ y
(node f t) [ σ ]t = node f (λ z → (t z) [ σ ]t )

\end{code}

----------------------------------

<span style="float:left;">[← Terms.Properties](Terms.Properties.html)</span>
<span style="float:right;">[Terms.Func →](Terms.Func.html)</span>

{% include UALib.Links.md %}
