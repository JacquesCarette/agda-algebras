---
layout: default
title : ClosureSystems.Properties module (The Agda Universal Algebra Library)
date : 2021-07-08
author: [agda-algebras development team][]
---

### Properties of Closure Systems and Operators


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ClosureSystems.Properties where

open import Agda.Primitive          using ( _⊔_ ; Level ) renaming ( Set to Type )
import Algebra.Definitions
open import Data.Product            using ( _,_ ; _×_ )
open import Function.Bundles        using ( _↔_ ; Inverse )
open import Relation.Binary.Bundles using ( Poset )
open import Relation.Binary.Core    using ( _Preserves_⟶_ )
import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning


open import ClosureSystems.Basic       using ( ClOp )
open import ClosureSystems.Definitions using ( Extensive )
open ClOp
open Inverse


module _ {ℓ ℓ₁ ℓ₂ : Level}{𝑨 : Poset ℓ ℓ₁ ℓ₂}(𝑪 : ClOp 𝑨) where
 open Poset 𝑨
 open ≤-Reasoning 𝑨

 private
  c = C 𝑪
  A = Carrier

 -- Theorem 1. If `𝑨 = (A , ≦)` is a poset and `c` is a closure operator on A, then
 --            ∀ (x y : A) → (x ≦ (c y) ↔ (c x) ≦ (c y))
 --
 clop→law⇒ : (x y : A) → x ≤ (c y) → (c x) ≤ (c y)
 clop→law⇒ x y x≤cy = begin
   c x     ≤⟨ isOrderPreserving 𝑪 x≤cy ⟩
   c (c y) ≈⟨ isIdempotent 𝑪 y ⟩
   c y ∎

 clop→law⇐ : (x y : A) → (c x) ≤ (c y) → x ≤ (c y)
 clop→law⇐ x y cx≤cy = begin
   x   ≤⟨ isExtensive 𝑪 ⟩
   c x ≤⟨ cx≤cy ⟩
   c y ∎

module _ {ℓ ℓ₁ ℓ₂ : Level}{𝑨 : Poset ℓ ℓ₁ ℓ₂} where
 open Poset 𝑨

 private
  A = Carrier

 open Algebra.Definitions (_≈_)

 -- The converse of Theorem 1 also holds.
 --
 -- Theorem 2. If `𝑨 = (A , ≤)` is a poset and `c : A → A` satisfies
 --            ∀ (x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y))
 --            then `c` is a closure operator on A.
 --
 clop←law : (c : A → A) → ((x y : A) → (x ≤ (c y) ↔ (c x) ≤ (c y)))
  →         Extensive _≤_ c × c Preserves _≤_ ⟶ _≤_ × IdempotentFun c

 clop←law c hyp  = e , (o , i)
  where
  h1 : ∀ {x y} → x ≤ (c y) → c x ≤ c y
  h1 {x}{y} = f (hyp x y)

  h2 : ∀ {x y} → c x ≤ c y → x ≤ (c y)
  h2 {x}{y} = f⁻¹ (hyp x y)

  e : Extensive _≤_ c
  e = h2 refl

  o : c Preserves _≤_ ⟶ _≤_
  o u = h1 (trans u e)

  i : IdempotentFun c
  i x = antisym (h1 refl) (h2 refl)

\end{code}




--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
