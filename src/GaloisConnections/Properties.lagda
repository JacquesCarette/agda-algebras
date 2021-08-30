---
layout: default
title : "GaloisConnections.Properties module (The Agda Universal Algebra Library)"
date : "2021-07-01"
author: "agda-algebras development team"
---

### <a id="basic-properties">Basic properties</a>

This is the [GaloisConnections.Properties][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GaloisConnections.Properties where

-- Imports from Agda and the Agda Standard Library  ---------------------------------------
open import Agda.Primitive          using ( _⊔_ ; Level ; lsuc ) renaming ( Set to Type )
open import Data.Product            using ( _,_ ; _×_ ) renaming ( proj₁ to fst )
open import Data.Product            using ( swap )
open import Function.Base           using ( _∘_ ; id )
open import Relation.Binary.Bundles using ( Poset )
open import Relation.Binary.Core    using ( REL )
open import Relation.Unary          using ( Pred ; _⊆_ )
import Relation.Binary.Structures as BS

-- Imports from agda-algebras --------------------------------------------------------------
open import GaloisConnections.Basic using (Galois ; ←→≥id ; →←≥id ; _⃗_ ; _⃖_ )

open Poset

\end{code}

#### <a id="the-poset-of-subsets-of-a-set">The poset of subsets of a set</a>

Here we define a type that represents the poset of subsets of a given set equipped with the usual set inclusion relation. (It seems there is no definition in the standard library of this important example of a poset; we should propose adding it.)

\begin{code}

module _ {α ρ : Level} {𝒜 : Type α} where

 _≐_ : Pred 𝒜 ρ → Pred 𝒜 ρ → Type (α ⊔ ρ)
 P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

 open BS.IsEquivalence renaming (refl to ref ; sym to symm ; trans to tran)

 ≐-iseqv : BS.IsEquivalence _≐_
 ref ≐-iseqv = id , id
 symm ≐-iseqv = swap
 tran ≐-iseqv (u₁ , u₂) (v₁ , v₂) = v₁ ∘ u₁ , u₂ ∘ v₂


module _ {α : Level} (ρ : Level) (𝒜 : Type α) where

 PosetOfSubsets : Poset (α ⊔ lsuc ρ) (α ⊔ ρ) (α ⊔ ρ)
 Carrier PosetOfSubsets = Pred 𝒜 ρ
 _≈_ PosetOfSubsets = _≐_
 _≤_ PosetOfSubsets = _⊆_
 isPartialOrder PosetOfSubsets =
  record { isPreorder = record { isEquivalence = ≐-iseqv
                               ; reflexive = fst
                               ; trans = λ u v → v ∘ u
                               }
         ; antisym = _,_
         }

\end{code}

A Binary relation from one poset to another induces a Galois connection, but only in a very special
situation, namely when all the involved sets are of the same size.  This is akin to the situation
with Adjunctions in Category Theory (unsurprisingly). In other words, there is likely a
unit/counit definition that is more level polymorphic.

\begin{code}

module _ {ℓ : Level}{𝒜 : Type ℓ} {ℬ : Type ℓ} where

 𝒫𝒜 : Poset (lsuc ℓ) ℓ ℓ
 𝒫ℬ : Poset (lsuc ℓ) ℓ ℓ
 𝒫𝒜 = PosetOfSubsets ℓ 𝒜
 𝒫ℬ = PosetOfSubsets ℓ ℬ

 -- Every binary relation from one poset to another induces a Galois connection.
 Rel→Gal : (R : REL 𝒜 ℬ ℓ) → Galois 𝒫𝒜 𝒫ℬ
 Rel→Gal R = record { F = _⃗ R
                    ; G = R ⃖_
                    ; GF≥id = λ _ → ←→≥id
                    ; FG≥id = λ _ → →←≥id }

\end{code}


--------------------

<span style="float:left;">[← GaloisConnections.Basic](GaloisConnections.Basic.html)</span>
<span style="float:right;">[ClosureSystems →](ClosureSystems.html)</span>

{% include UALib.Links.md %}

