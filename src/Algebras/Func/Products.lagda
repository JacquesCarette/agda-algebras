---
layout: default
title : "Algebras.Func.Products module (Agda Universal Algebra Library)"
date : "2021-07-03"
author: "agda-algebras development team"
---

#### <a id="products-of-setoidalgebras">Products of Setoid Algebras</a>

This is the [Algebras.Func.Products][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature)

module Algebras.Func.Products {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library --------------------------------
open import Agda.Primitive   using ( lsuc ; _⊔_ ; Level ) renaming ( Set to Type )
open import Data.Product     using ( _,_ ; Σ-syntax ; _×_ )
open import Function.Base    using ( flip )
open import Function.Bundles using ( Func )
open import Relation.Binary  using ( Setoid ;  IsEquivalence ; Decidable )
open import Relation.Binary.PropositionalEquality
                             using ( refl ; _≡_ )
open import Relation.Unary   using ( Pred ; _⊆_ ; _∈_ )

open Func          using ( cong ) renaming ( f to _<$>_ )
open Setoid        using ( Carrier ; _≈_ ) renaming ( isEquivalence to isEqv )
open IsEquivalence using () renaming ( refl to reflE ; sym to symE ; trans to transE )


-- Imports from agda-algebras -----------------------------------------------------
open import Overture.Preliminaries      using ( ∣_∣; ∥_∥)
open import Overture.Surjective         using ( proj ; projIsOnto ) renaming ( IsSurjective to onto )
open import Algebras.Func.Basic {𝑆 = 𝑆} using ( ⟦_⟧ ; SetoidAlgebra ; _̂_ ; ov ; 𝕌[_])

private variable α ρ ι : Level

open SetoidAlgebra

⨅ : {I : Type ι }(𝒜 : I → SetoidAlgebra α ρ) → SetoidAlgebra (α ⊔ ι) (ρ ⊔ ι)

Domain (⨅ {I} 𝒜) =

 record { Carrier = ∀ i → Carrier (Domain (𝒜 i))

        ; _≈_ = λ a b → ∀ i → Domain (𝒜 i) ._≈_ (a i) (b i)

        ; isEquivalence =
           record { refl  =     λ i → reflE  (isEqv (Domain (𝒜 i)))
                  ; sym   =   λ x i → symE   (isEqv (Domain (𝒜 i)))(x i)
                  ; trans = λ x y i → transE (isEqv (Domain (𝒜 i)))(x i)(y i)
                  }
        }

(Interp (⨅ {I} 𝒜)) <$> (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
cong (Interp (⨅ {I} 𝒜)) (refl , f=g ) = λ i → cong  (Interp (𝒜 i)) (refl , flip f=g i )

\end{code}

#### <a id="products-of-classes-of-setoidalgebras">Products of classes of SetoidAlgebras</a>

\begin{code}

module _ {𝒦 : Pred (SetoidAlgebra α ρ) (ov α)} where

 ℑ : Type (ov(α ⊔ ρ))
 ℑ = Σ[ 𝑨 ∈ (SetoidAlgebra α ρ) ] 𝑨 ∈ 𝒦


 𝔄 : ℑ → SetoidAlgebra α ρ
 𝔄 i = ∣ i ∣

 class-product : SetoidAlgebra (ov (α ⊔ ρ)) _
 class-product = ⨅ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class,
so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the
product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.


#### Proving the coordinate projections are surjective

Suppose `I` is an index type and `𝒜 : I → SetoidAlgebra α ρ` is an indexed collection of algebras.
Let `⨅ 𝒜` be the product algebra defined above.  Given `i : I`, consider the projection of `⨅ 𝒜`
onto the `i-th` coordinate.  Of course this projection ought to be a surjective map from `⨅ 𝒜` onto
`𝒜 i`.  However, this is impossible if `I` is just an arbitrary type.  Indeed, we must have an
equality defined on `I` and this equality must be decidable, and we must assume that
each factor of the product is nonempty.  In the [Overture.Surjective][] module
we showed how to define a *decidable index type* in Agda. Here we use this to prove that the
projection of a product of algebras over such an index type is surjective.

\begin{code}

module _ {I : Type ι}                    -- index type
         {_≟_ : Decidable{A = I} _≡_}    -- with decidable equality

         {𝒜 : I → SetoidAlgebra α ρ}     -- indexed collection of algebras
         {𝒜I : ∀ i → 𝕌[ 𝒜 i ] }          -- each of which is nonempty
         where

 ProjAlgIsOnto : ∀{i} → Σ[ h ∈ (𝕌[ ⨅ 𝒜 ] → 𝕌[ 𝒜 i ]) ] onto h
 ProjAlgIsOnto {i} = (proj _≟_ 𝒜I i) , projIsOnto _≟_ 𝒜I

\end{code}

--------------------------------

<span style="float:left;">[← Algebras.Func.Basic](Algebras.Func.Basic.html)</span>
<span style="float:right;">[Algebras.Func.Congruences →](Algebras.Func.Congruences.html)</span>

{% include UALib.Links.md %}
