---
layout: default
title : Varieties.Setoid.FreeAlgebras module (Agda Universal Algebra Library)
date : 2021-06-29
author: [agda-algebras development team][]
---

### <a id="free-algebras-and-birkhoffs-theorem-setoid-version">Free Algebras and Birkhoff's Theorem (Setoid version)</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Setoid.FreeAlgebras {𝑆 : Signature 𝓞 𝓥} where


-- Imports from Agda and the Agda Standard Library ---------------------
open import Agda.Primitive using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type )
open import Data.Product   using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base  using ( id )
open import Relation.Unary using ( Pred  ; _∈_ )
open import Relation.Binary.PropositionalEquality
                           using ( refl )

-- Imports from the Agda Universal Algebra Library -------------------------------------------
open import Overture.Preliminaries             using ( ∣_∣ )
open import Overture.Inverses                  using ( IsSurjective ; Image_∋_ ; Inv ; InvIsInv ; eq )
open import Algebras.Setoid.Products   {𝑆 = 𝑆} using ( ⨅ )
open import Algebras.Setoid.Basic      {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ) renaming ( ⟦_⟧ to ⟦_⟧s )
open import Homomorphisms.Setoid.Basic {𝑆 = 𝑆} using ( hom ; epi )
open import Terms.Setoid.Basic         {𝑆 = 𝑆} using ( 𝑻 )
open import Varieties.Setoid.EquationalLogic
                                       {𝑆 = 𝑆} using ( Eq ; _⊫_ ; module TermModel ; Mod ; Th)

private variable
 α χ ρ ℓ : Level


module _ {X : Type χ}{𝒦 : Pred (SetoidAlgebra α ρ) ℓ} where

 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ eq

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

\end{code}

#### <a id="the-free-algebra">The free algebra</a>

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.

\begin{code}

 -- The relatively free algebra (relative to Th 𝒦) is called `M`
 -- and is derived from `TermSetoid Γ` and `TermInterp Γ` and
 -- imported from the EquationalLogic module.
 open TermModel {X = X}{ι = (ℓ ⊔ ov(α ⊔ χ ⊔ ρ))}{I = ℐ} ℰ

 𝔽 : SetoidAlgebra _ _
 𝔽 = M X

 epi𝔽 : epi (𝑻 X) 𝔽
 epi𝔽 = record { map = id ; is-epi = (λ 𝑓 a → refl) , λ y → eq y refl }

 open epi

 hom𝔽 : hom (𝑻 X) 𝔽
 hom𝔽 = epi-to-hom epi𝔽

 hom𝔽-is-epic : IsSurjective ∣ hom𝔽 ∣
 hom𝔽-is-epic = snd (is-epi epi𝔽)

 -- 𝕍𝒦 : Pred (SetoidAlgebra _ _) _
 -- 𝕍𝒦 = V 𝒦

 -- 𝔽-ModTh-epi : (𝑨 : SetoidAlgebra _ _) → 𝑨 ∈ Mod (Th 𝕍𝒦) → epi 𝔽 𝑨
 -- 𝔽-ModTh-epi 𝑨 AinMTV = ?


\end{code}


To be continued...

(TODO: complete this module)

--------------------------------

<br>

[← Varieties.Setoid.Closure](Varieties.Setoid.Closure.html)
<span style="float:right;">[Structures →](Structures.html)</span>

{% include UALib.Links.md %}

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team