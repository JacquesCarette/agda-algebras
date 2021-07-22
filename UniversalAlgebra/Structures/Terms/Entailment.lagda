---
layout: default
title : Structures.Terms.Entailment
date : 2021-07-02
author: [agda-algebras development team][]
---


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Terms.Entailment where

open import Agda.Primitive   using    ( _⊔_   ;  Level
                                      ; lsuc           )
                             renaming ( Set   to Type
                                      ; lzero to ℓ₀    )
open import Relation.Unary   using    ( Pred  ;  _∈_   )
open import Data.Nat         using    ( ℕ              )
open import Data.Fin.Base    using    ( Fin            )
open import Data.Product     using    ( _,_   ;  _×_   )
                             renaming ( proj₁    to  fst
                                      ; proj₂    to  snd   )

-- -- Imports from agda-algebras --------------------------------------
open import Overture.Preliminaries  using ( _≈_ )
open import Structures.Records      using ( signature ; structure )
open import Structures.Terms.Basic

open signature
open structure

-- ℓ₁ : Level
-- ℓ₁ = lsuc ℓ₀
private variable
 𝓞₀ 𝓥₀ 𝓞₁ 𝓥₁ : Level
 𝐹 : signature 𝓞₀ 𝓥₀
 𝑅 : signature 𝓞₁ 𝓥₁
 χ : Level
 X : Type χ
 α ρ ℓ : Level

_⊧_≈_ : structure 𝐹 𝑅 {α}{ρ} → Term X → Term X → Type _
𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

_⊧_≋_ : Pred(structure 𝐹 𝑅 {α}{ρ}) ℓ → Term X → Term X → Type _
𝒦 ⊧ p ≋ q = ∀{𝑨 : structure _ _} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

-- Theories
Th : Pred (structure 𝐹 𝑅{α}{ρ}) ℓ → Pred(Term X × Term X) _ -- (ℓ₁ ⊔ χ)
Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

-- Models
Mod : Pred(Term X × Term X) ℓ  → Pred(structure 𝐹 𝑅 {α} {ρ}) _  -- (χ ⊔ ℓ₀)
Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q

fMod : {n : ℕ} → (Fin n → (Term X × Term X)) → Pred(structure 𝐹 𝑅 {α} {ρ}) _
fMod ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ fst (ℰ i) ≈ snd (ℰ i)

\end{code}

The entailment ℰ ⊢ p ≈ q is valid iff p ≈ q holds in all models that satify all equations in ℰ.

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

