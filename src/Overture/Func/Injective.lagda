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

module Overture.Func.Injective
 {α ρᵃ β ρᵇ}{𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

-- Imports from Agda and the Agda Standard Library -------------
open import Agda.Primitive       using ( _⊔_ ; Level ) renaming ( Set to Type )
open import Function.Bundles     using ( Func ; Injection )
open import Relation.Binary.Core using ( _Preserves_⟶_ )
import Function.Definitions as FD

-- Imports from agda-algebras -----------------------------------------------
open import Overture.Func.Preliminaries using ( _⟶_ )
open import Overture.Func.Inverses      using ( Image_∋_ ; Inv )
open import Overture.Injective          using ( module compose )

private variable
 γ ρᶜ : Level

\end{code}

We can prove that, when `f` is injective, the range-restricted right-inverse `Inv`, defined in [Overture.Setoid.Inverse][], is also the (range-restricted) left-inverse.

\begin{code}

open Injection {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_)
open Setoid 𝑨 using () renaming (Carrier to A; _≈_ to _≈₁_)
open Setoid 𝑩 using ( trans ; sym ) renaming (Carrier to B; _≈_ to _≈₂_)
open Func {a = α}{ρᵃ}{β}{ρᵇ}{From = 𝑨}{To = 𝑩} renaming (f to _⟨$⟩_ )
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


module _ {𝑪 : Setoid γ ρᶜ} where
 open Setoid 𝑪 using ( sym ) renaming (Carrier to C; _≈_ to _≈₃_)
 open compose {A = A}{B}{C} _≈₁_ _≈₂_ _≈₃_ using ( ∘-injective )


 -- Composition is injective.

 ∘-injection : Injection 𝑨 𝑩 → Injection 𝑩 𝑪 → Injection 𝑨 𝑪
 ∘-injection fi gi = record { f = λ x → apg (apf x)
                            ; cong = conggf
                            ; injective = ∘-injective (injective fi) (injective gi)
                            }
  where
  open Injection
  apf : A → B
  apf = f fi
  apg : B → C
  apg = f gi
  conggf : (λ x → apg (apf x)) Preserves _≈₁_ ⟶ _≈₃_
  conggf {x}{y} x≈y = cong gi (cong fi x≈y)

\end{code}

--------------------------------------

<span style="float:left;">[← Overture.Setoid.Inverses](Overture.Func.Inverses.html)</span>
<span style="float:right;">[Overture.Setoid.Surjective →](Overture.Func.Surjective.html)</span>

{% include UALib.Links.md %}

