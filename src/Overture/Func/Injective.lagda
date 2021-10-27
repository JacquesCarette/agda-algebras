---
layout: default
title : "Overture.Func.Injective module"
date : "2021-09-13"
author: "the agda-algebras development team"
---

### <a id="injective-functions-on-setoids">Injective functions on setoids</a>

This is the [Overture.Func.Injective][] module of the [agda-algebras][] library.

We say that a function `f : A → B` from one setoid (A , ≈₀) to another (B , ≈₁) is *injective* (or *monic*) provided the following implications hold:  ∀ a₀ a₁ if f ⟨$⟩ a₀ ≈₁ f ⟨$⟩ a₁, then a₀ ≈₀ a₁.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Relation.Binary using ( Setoid )

module Overture.Func.Injective where


-- Imports from Agda and the Agda Standard Library -------------
open import Agda.Primitive       using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Function.Bundles     using ( Injection ) renaming ( Func to _⟶_ )
open import Function.Base        using ( _∘_ ; id )
open import Relation.Binary.Core using ( _Preserves_⟶_ )
open import Relation.Binary using ( Rel )
import Function.Definitions as FD

-- Imports from agda-algebras -----------------------------------------------
open import Overture.Func.Preliminaries using ( 𝑖𝑑 )
open import Overture.Func.Inverses      using ( Image_∋_ ; Inv )

private variable
 α β γ ρᵃ ρᵇ ρᶜ ℓ₁ ℓ₂ ℓ₃ : Level

\end{code}

A function `f : A ⟶ B` from one setoid `(A , ≈₀)` to another
`(B , ≈₁)` is called *injective* provided `∀ a₀ a₁`, if `f ⟨$⟩ a₀ ≈₁ f ⟨$⟩
a₁`, then `a₀ ≈₀ a₁`.  The [Agda Standard Library][] defines a type representing
injective functions on bare types and we use this type (called `Injective`) to
define our own type representing the property of being an injective function on
setoids (called `IsInjective`).

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 open Injection {From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_)
 open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩 using ( trans ; sym ) renaming (Carrier to B; _≈_ to _≈₂_)
 open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_ )
 open FD _≈₁_ _≈₂_

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective (_⟨$⟩_ f)

 open Image_∋_

 -- Inverse of an injective function preserves setoid equalities
 LeftInvPreserves≈ : (F : Injection 𝑨 𝑩)
                     {b₀ b₁ : B}(u : Image (function F) ∋ b₀)(v : Image (function F) ∋ b₁)
  →                  b₀ ≈₂ b₁ → (Inv (function F) u) ≈₁ (Inv (function F) v)

 LeftInvPreserves≈ F {b₀}{b₁} (eq a₀ x₀) (eq a₁ x₁) bb = Goal
  where
  fa₀≈fa₁ : (F ⟨$⟩ a₀) ≈₂ (F ⟨$⟩ a₁)
  fa₀≈fa₁ = trans (sym x₀) (trans bb x₁)
  Goal : a₀ ≈₁ a₁
  Goal = injective F fa₀≈fa₁



module compose {A : Type α}{B : Type β}{C : Type γ}
               (_≈₁_ : Rel A ℓ₁) -- Equality over A
               (_≈₂_ : Rel B ℓ₂) -- Equality over B
               (_≈₃_ : Rel C ℓ₃) -- Equality over C
               where

 open FD {A = A} {B} _≈₁_ _≈₂_ using () renaming ( Injective to InjectiveAB )
 open FD {A = B} {C} _≈₂_ _≈₃_ using () renaming ( Injective to InjectiveBC )
 open FD {A = A} {C} _≈₁_ _≈₃_ using () renaming ( Injective to InjectiveAC )

 ∘-injective-func : {f : A → B}{g : B → C}
  →            InjectiveAB f → InjectiveBC g → InjectiveAC (g ∘ f)
 ∘-injective-func finj ginj = λ z → finj (ginj z)


module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} {𝑪 : Setoid γ ρᶜ} where

 open Injection {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_)
 open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
 open Setoid 𝑩 using ( trans ; sym ) renaming (Carrier to B; _≈_ to _≈₂_)
 open _⟶_ {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_ )
 open Setoid 𝑪 using ( sym ) renaming (Carrier to C; _≈_ to _≈₃_)
 open compose {A = A}{B}{C} _≈₁_ _≈₂_ _≈₃_ using ( ∘-injective-func )


 -- Composition is injective.

 ∘-injection : Injection 𝑨 𝑩 → Injection 𝑩 𝑪 → Injection 𝑨 𝑪
 ∘-injection fi gi = record { f = λ x → apg (apf x)
                            ; cong = conggf
                            ; injective = ∘-injective-func (injective fi) (injective gi)
                            }
  where
  open Injection
  apf : A → B
  apf = f fi
  apg : B → C
  apg = f gi
  conggf : (λ x → apg (apf x)) Preserves _≈₁_ ⟶ _≈₃_
  conggf {x}{y} x≈y = cong gi (cong fi x≈y)


id-is-injective : {𝑨 : Setoid α ρᵃ} → IsInjective{𝑨 = 𝑨}{𝑨} 𝑖𝑑
id-is-injective = id

\end{code}

--------------------------------------

<span style="float:left;">[← Overture.Func.Inverses](Overture.Func.Inverses.html)</span>
<span style="float:right;">[Overture.Func.Surjective →](Overture.Func.Surjective.html)</span>

{% include UALib.Links.md %}

