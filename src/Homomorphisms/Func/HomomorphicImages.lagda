---
layout: default
title : "Homomorphisms.Func.HomomorphicImages module (The Agda Universal Algebra Library)"
date : "2021-09-14"
author: "agda-algebras development team"
---

#### <a id="homomorphic-images-of-setoid-algebras">Homomorphic images of setoid algebras</a>

This is the [Homomorphisms.Func.HomomorphicImages][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Homomorphisms.Func.HomomorphicImages {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------
open import Agda.Primitive  using ( _⊔_ ; lsuc )     renaming ( Set to Type )
open import Data.Product    using ( _,_ ; Σ-syntax ) renaming ( _×_ to _∧_ ; proj₁ to fst ; proj₂ to snd )
open import Function        using ( Func ; _on_ ; _∘_ )
open import Level           using ( Level )
open import Relation.Binary using ( Setoid ; _Preserves_⟶_ )
open import Relation.Unary  using ( Pred ; _∈_ )
open import Relation.Binary.PropositionalEquality as ≡ using ()

-- Imports from the Agda Universal Algebra Library ---------------------------------------------
open import Overture.Preliminaries                using ( ∣_∣ ; ∥_∥ ; transport )
open import Overture.Func.Preliminaries           using ( lift∼lower )
open import Overture.Func.Inverses                using ( Ran ; _range ; _preimage ; _image ; Inv
                                                        ; _preimage≈image ; InvIsInverseʳ ; Image_∋_ )
open import Overture.Func.Surjective              using ( IsSurjective )
open import Algebras.Func.Basic           {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; _̂_ ; ⟦_⟧ ; Lift-Alg ; 𝕌[_] )
open import Homomorphisms.Func.Basic      {𝑆 = 𝑆} using ( hom ; IsHom )
open import Homomorphisms.Func.Properties {𝑆 = 𝑆} using ( Lift-hom ; 𝓁𝒾𝒻𝓉 ; lift-hom-lemma )

private variable
 α ρᵃ β ρᵇ : Level

\end{code}

We begin with what seems, for our purposes, the most useful way to represent the class of *homomorphic images* of an algebra in dependent type theory.

\begin{code}

_IsHomImageOf_ : (𝑩 : SetoidAlgebra β ρᵇ)(𝑨 : SetoidAlgebra α ρᵃ) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : SetoidAlgebra α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov (β ⊔ ρᵇ))
HomImages {β = β}{ρᵇ = ρᵇ} 𝑨 = Σ[ 𝑩 ∈ SetoidAlgebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

\end{code}

These types should be self-explanatory, but just to be sure, let's describe the Sigma type appearing in the second definition. Given an `𝑆`-algebra `𝑨 : SetoidAlgebra α ρ`, the type `HomImages 𝑨` denotes the class of algebras `𝑩 : SetoidAlgebra β ρ` with a map `φ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣` such that `φ` is a surjective homomorphism.

#### <a id="constructing an algebra from the image of a hom">The image algebra of a hom</a>

Here we show how to construct a SetoidAlgebra (called `ImageAlgebra` below) that is the image of given hom.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}{𝑩 : SetoidAlgebra β ρᵇ} where
 open SetoidAlgebra 𝑨 using (Interp) renaming (Domain to A )
 open SetoidAlgebra 𝑩 using () renaming (Domain to B ; Interp to InterpB )

 open Setoid A using ( ) renaming ( _≈_ to _≈₁_ ; Carrier to ∣A∣)
 open Setoid B using ( reflexive ) renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ ; Carrier to ∣B∣)

 open Func using ( cong ) renaming (f to _⟨$⟩_ )
 open IsHom

 HomImageOf[_] : hom 𝑨 𝑩 → SetoidAlgebra (α ⊔ β ⊔ ρᵇ) ρᵇ
 HomImageOf[ h ] =
  record { Domain = Ran ∣ h ∣ ; Interp = record { f = f' ; cong = cong' } }
   where
   open Setoid (⟦ 𝑆 ⟧ (Ran ∣ h ∣)) using () renaming (Carrier to SRanh ; _≈_ to _≈₃_ ; refl to refl₃ )

   hhom : ∀ {𝑓}(x : ∥ 𝑆 ∥ 𝑓 → ∣ h ∣ range )
    →     (∣ h ∣ ⟨$⟩ (𝑓 ̂ 𝑨) ((∣ h ∣ preimage) ∘ x)) ≈₂ (𝑓 ̂ 𝑩) ((∣ h ∣ image) ∘ x)

   hhom {𝑓} x = trans₂ (compatible ∥ h ∥) (cong InterpB (≡.refl , (∣ h ∣ preimage≈image) ∘ x))

   f' : SRanh → ∣ h ∣ range
   f' (𝑓 , x) = (𝑓 ̂ 𝑩)((∣ h ∣ image)∘ x)       -- b : the image in ∣B∣
                , (𝑓 ̂ 𝑨)((∣ h ∣ preimage) ∘ x) -- a : the preimage in ∣A∣
                , hhom x                        -- p : proof that `(∣ h ∣ ⟨$⟩ a) ≈₂ b`

   cong' : ∀ {x y} → x ≈₃ y → ((∣ h ∣ image) (f' x)) ≈₂ ((∣ h ∣ image) (f' y))
   cong' {(𝑓 , u)} {(.𝑓 , v)} (≡.refl , EqA) = Goal

    where

    -- Alternative formulation of the goal:
    goal : (𝑓 ̂ 𝑩)(λ i → ((∣ h ∣ image)(u i))) ≈₂ (𝑓 ̂ 𝑩)(λ i → ((∣ h ∣ image) (v i)))
    goal = cong InterpB (≡.refl , EqA )

    Goal : (∣ h ∣ image) (f' (𝑓 , u)) ≈₂ (∣ h ∣ image) (f' (𝑓 , v))
    Goal = goal

    -- Note: `EqA : ∀ i → (∣ h ∣ image) (u i) ≈₂ (∣ h ∣ image) (v i)`

\end{code}


#### <a id="homomorphic-images-of-classes-of-setoid-algebras">Homomorphic images of classes of setoid algebras</a>

Given a class `𝒦` of `𝑆`-algebras, we need a type that expresses the assertion that a given algebra is a homomorphic image of some algebra in the class, as well as a type that represents all such homomorphic images.

\begin{code}

IsHomImageOfClass : {𝒦 : Pred (SetoidAlgebra α ρᵃ)(lsuc α)} → SetoidAlgebra α ρᵃ → Type (ov (α ⊔ ρᵃ))
IsHomImageOfClass {𝒦 = 𝒦} 𝑩 = Σ[ 𝑨 ∈ SetoidAlgebra _ _ ] ((𝑨 ∈ 𝒦) ∧ (𝑩 IsHomImageOf 𝑨))

HomImageOfClass : Pred (SetoidAlgebra α ρᵃ) (lsuc α) → Type (ov (α ⊔ ρᵃ))
HomImageOfClass 𝒦 = Σ[ 𝑩 ∈ SetoidAlgebra _ _ ] IsHomImageOfClass {𝒦 = 𝒦} 𝑩

\end{code}


#### <a id="lifting-tools">Lifting tools</a>

Here are some tools that have been useful (e.g., in the road to the proof of Birkhoff's HSP theorem). The first states and proves the simple fact that the lift of an epimorphism is an epimorphism.

\begin{code}

module _ {𝑨 : SetoidAlgebra α ρᵃ}
         {𝑩 : SetoidAlgebra β ρᵇ} where

 open SetoidAlgebra 𝑨 using ()              renaming ( Domain to A )
 open SetoidAlgebra 𝑩 using ()              renaming ( Domain to B )
 open Setoid B        using ( sym ; trans ) renaming ( _≈_ to _≈₂_ )

 open Func            using ( cong )        renaming ( f to _⟨$⟩_ )
 open Level

 Lift-epi-is-epi : (h : hom 𝑨 𝑩)(ℓᵃ ℓᵇ : Level)
  →                IsSurjective ∣ h ∣ → IsSurjective ∣ Lift-hom {𝑨 = 𝑨}{𝑩} h ℓᵃ ℓᵇ ∣

 Lift-epi-is-epi h ℓᵃ ℓᵇ hepi {b} = Goal
  where
  open SetoidAlgebra (Lift-Alg 𝑩 ℓᵇ) using () renaming (Domain to lB )
  open Setoid lB using () renaming ( _≈_ to _≈ₗ₂_ )

  a : 𝕌[ 𝑨 ]
  a = Inv ∣ h ∣ hepi

  lem1 : b ≈ₗ₂ (lift (lower b))
  lem1 = lift∼lower {𝑨 = B} b

  lem2' : (lower b) ≈₂ (∣ h ∣ ⟨$⟩ a)
  lem2' = sym  (InvIsInverseʳ hepi)

  lem2 : (lift (lower b)) ≈ₗ₂ (lift (∣ h ∣ ⟨$⟩ a))
  lem2 = cong{From = B} ∣ 𝓁𝒾𝒻𝓉{𝑨 = 𝑩}{ℓ = ℓᵇ} ∣ lem2'

  lem3 : (lift (∣ h ∣ ⟨$⟩ a)) ≈ₗ₂ ((∣ Lift-hom h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a))
  lem3 = lift-hom-lemma h a ℓᵃ ℓᵇ

  η : b ≈ₗ₂ (∣ Lift-hom h ℓᵃ ℓᵇ ∣ ⟨$⟩ lift a)
  η = trans lem1 (trans lem2 lem3)

  Goal : Image ∣ Lift-hom h ℓᵃ ℓᵇ ∣ ∋ b
  Goal = Image_∋_.eq (lift a) η


 Lift-Alg-hom-image : (ℓᵃ ℓᵇ : Level) → 𝑩 IsHomImageOf 𝑨
  →                   (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf (Lift-Alg 𝑨 ℓᵃ)

 Lift-Alg-hom-image ℓᵃ ℓᵇ ((φ , φhom) , φepic) = Goal
  where
  lφ : hom (Lift-Alg 𝑨 ℓᵃ) (Lift-Alg 𝑩 ℓᵇ)
  lφ = Lift-hom {𝑨 = 𝑨}{𝑩} (φ , φhom) ℓᵃ ℓᵇ

  lφepic : IsSurjective ∣ lφ ∣
  lφepic = Lift-epi-is-epi (φ , φhom) ℓᵃ ℓᵇ φepic
  Goal : (Lift-Alg 𝑩 ℓᵇ) IsHomImageOf (Lift-Alg 𝑨 ℓᵃ)
  Goal = lφ , lφepic

\end{code}

--------------------------------------

<span style="float:left;">[← Homomorphisms.Func.Isomorphisms](Homomorphisms.Func.Isomorphisms.html)</span>
<span style="float:right;">[Terms →](Terms.html)</span>

{% include UALib.Links.md %}