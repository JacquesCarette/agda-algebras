n---
layout: default
title : "Varieties.Func.FreeAlgebras module (Agda Universal Algebra Library)"
date : "2021-06-29"
author: "agda-algebras development team"
---

#### <a id="free-setoid-algebras">Free setoid algebras</a>

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Varieties.Func.FreeAlgebras {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ------------------------------------------------
open import Agda.Primitive   using () renaming ( Set to Type )
open import Data.Product     using ( Σ-syntax ; _,_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function         using ( _∘_ ; id )
open import Function.Bundles using ( Func )
open import Level
open import Relation.Binary  using ( Setoid )
open import Relation.Unary   using ( Pred ; _∈_ ; _⊆_ )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- -- Imports from the Agda Universal Algebra Library ---------------------------------------------------
open import Overture.Preliminaries                  using ( ∣_∣ ; ∥_∥ )
open import Overture.Func.Preliminaries             using ( _⟶_ )
open import Overture.Func.Inverses                  using ( eq )
open import Overture.Func.Surjective                using ( IsSurjective )
open import Relations.Func.Discrete                 using ( fkerPred )
open import Algebras.Func.Basic             {𝑆 = 𝑆} using ( SetoidAlgebra ; ov ; Lift-Alg )
open import Homomorphisms.Func.Basic        {𝑆 = 𝑆} using ( epi ; IsEpi ; IsHom ; hom ; epi→hom )
open import Homomorphisms.Func.Properties   {𝑆 = 𝑆} using ( ∘-epi ; ToLift-epi )
open import Terms.Basic                     {𝑆 = 𝑆} using ( Term ; ℊ )
open import Terms.Func.Basic                {𝑆 = 𝑆} using ( 𝑻 ; _≐_ ; module Environment )
open import Terms.Func.Properties           {𝑆 = 𝑆} using ( free-lift )
open import Terms.Func.Operations           {𝑆 = 𝑆} using ( free-lift-interp )
open import Varieties.Func.SoundAndComplete {𝑆 = 𝑆} using ( Eq ; _⊫_ ; _≈̇_ ; _⊢_▹_≈_
                                                          ; module Soundness
                                                          ; module FreeAlgebra
                                                          ; ThPred ; ModPred )
open import Varieties.Func.Closure          {𝑆 = 𝑆} using ( V ; S )
open import Varieties.Func.Preservation  {𝑆 = 𝑆} using ( classIds-⊆-VIds ; S-id1 ; S-id2 )

open Func using ( cong ) renaming ( f to _⟨$⟩_ )
open SetoidAlgebra using ( Domain )


private variable
 χ : Level
\end{code}

In the code below, `X` will play the role of an arbitrary collection of variables; it would suffice to take `X` to be the cardinality of the largest algebra in 𝒦, but since we don't know that cardinality, we leave `X` aribtrary for now.

Alternatively, we could let `X` be the product of all algebras in the class `𝒦`, like so.

`𝕏 : Type oα`  
`𝕏 = Carrier ( Domain (⨅ (𝔄{𝒦 = S 𝒦})) )`

\begin{code}

module FreeHom (χ : Level){α : Level}(𝒦 : Pred (SetoidAlgebra α α) (ov α)) where
 private
  oα = ov α
  oαχ = ov (α ⊔ χ)
  ooα = ov oα

 open Eq

\end{code}

We now define the algebra `𝔽`, which plays the role of the relatively free algebra, along with the natural epimorphism `epi𝔽 : epi (𝑻 𝕏) 𝔽` from `𝑻 𝕏` to `𝔽`.
The relatively free algebra (relative to `Th 𝒦`) is called `M` and is derived from `TermSetoid 𝕏` and `TermInterp 𝕏` and imported from the EquationalLogic module.

\begin{code}

 -- ℐ indexes the collection of equations modeled by 𝒦
 ℐ : Type oαχ
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ ((lhs eq) ≈̇ (rhs eq))

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

 ℰ⊢[_]▹Th𝒦 : (X : Type χ) → ∀{p q} → ℰ ⊢ X ▹ p ≈ q → 𝒦 ⊫ (p ≈̇ q)
 ℰ⊢[ X ]▹Th𝒦 x 𝑨 kA = sound (λ i ρ → ∥ i ∥ 𝑨 kA ρ) x
  where open Soundness ℰ 𝑨

 ----------- THE RELATIVELY FREE ALGEBRA -----------
 open FreeAlgebra {ι = oαχ}{I = ℐ} ℰ using ( 𝔽[_] )

\end{code}

Next we define an epimorphism from `𝑻 X` onto the relatively free algebra `𝔽[ X ]`.  Of course, the kernel of this epimorphism will be the congruence of `𝑻 X` defined by identities modeled by (`S 𝒦`, hence) `𝒦`.

\begin{code}

 epi𝔽[_] : (X : Type χ) → epi (𝑻 X) 𝔽[ X ]
 epi𝔽[ X ] = h , hepi
  where
  open SetoidAlgebra 𝔽[ X ] using () renaming ( Domain to F ; Interp to InterpF )
  open Setoid F using () renaming ( _≈_  to _≈F≈_ ; refl to reflF )

  open SetoidAlgebra (𝑻 X) using () renaming (Domain to TX)
  open Setoid TX using () renaming ( _≈_ to _≈T≈_ ; refl to reflT )


  open _≐_ ; open IsEpi ; open IsHom

  c : ∀ {x y} → x ≈T≈ y → x ≈F≈ y
  c (rfl {x}{y} ≡.refl) = reflF
  c (gnl {f}{s}{t} x) = cong InterpF (≡.refl , c ∘ x)

  h : TX ⟶ F
  h = record { f = id ; cong = c }

  hepi : IsEpi (𝑻 X) 𝔽[ X ] h
  compatible (isHom hepi) = cong h reflT
  isSurjective hepi {y} = eq y reflF


 hom𝔽[_] : (X : Type χ) → hom (𝑻 X) 𝔽[ X ]
 hom𝔽[ X ] = epi→hom (𝑻 X) 𝔽[ X ] epi𝔽[ X ]

 hom𝔽[_]-is-epic : (X : Type χ) → IsSurjective ∣ hom𝔽[ X ] ∣
 hom𝔽[ X ]-is-epic = IsEpi.isSurjective (snd (epi𝔽[ X ]))


 class-models-kernel : ∀{X p q} → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣ → 𝒦 ⊫ (p ≈̇ q)
 class-models-kernel {X = X}{p}{q} pKq = ℰ⊢[ X ]▹Th𝒦 pKq

 kernel-in-theory : {X : Type χ} → fkerPred ∣ hom𝔽[ X ] ∣ ⊆ ThPred (V 𝒦)
 kernel-in-theory {X = X} {p , q} pKq vkA x = classIds-⊆-VIds{p = p}{q}
                                      (class-models-kernel pKq) vkA x


 module _  {X : Type χ} {𝑨 : SetoidAlgebra α α}{sA : 𝑨 ∈ S 𝒦} where
  open Environment 𝑨 using ( Equal )
  ker𝔽⊆Equal : ∀{p q} → (p , q) ∈ fkerPred ∣ hom𝔽[ X ] ∣ → Equal p q
  ker𝔽⊆Equal{p = p}{q} x = S-id1{p = p}{q} (ℰ⊢[ X ]▹Th𝒦 x) 𝑨 sA


 𝒦⊫→ℰ⊢ : {X : Type χ} → ∀{p q} → 𝒦 ⊫ (p ≈̇ q) → ℰ ⊢ X ▹ p ≈ q
 𝒦⊫→ℰ⊢ {p = p} {q} pKq = hyp ((p ≈̇ q) , pKq) where open _⊢_▹_≈_ using (hyp)


------------------------------------------------------------------------------

module _ {α : Level}(𝑨 : SetoidAlgebra α α)(𝒦 : Pred (SetoidAlgebra α α) (ov α)) where

 private
  oα = ov α

 open FreeHom α 𝒦
 open FreeAlgebra {ι = oα}{I = ℐ} ℰ using ( 𝔽[_] )
 open SetoidAlgebra 𝑨 using( Interp ) renaming (Domain to A)
 open Setoid A using ( trans ; sym ; refl ) renaming ( Carrier to ∣A∣ )

 𝔽-ModTh-epi : (𝑨 ∈ ModPred{X = ∣A∣} (ThPred{X = ∣A∣} (V 𝒦))) → epi 𝔽[ ∣A∣ ] 𝑨
 𝔽-ModTh-epi A∈ModThK = φ , isEpi
   where
   open IsEpi
   open IsHom

   φ : (Domain 𝔽[ ∣A∣ ]) ⟶ A
   _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
   cong φ {p} {q} pq = trans (sym (free-lift-interp{𝑨 = 𝑨} id p))
                      (trans (A∈ModThK{p = p}{q} (kernel-in-theory pq) id)
                      (free-lift-interp{𝑨 = 𝑨} id q))

   isEpi : IsEpi 𝔽[ ∣A∣ ] 𝑨 φ
   compatible (isHom isEpi) = cong Interp (≡.refl , (λ _ → refl))
   isSurjective isEpi {y} = eq (ℊ y) refl


 𝔽-ModTh-epi-lift : (𝑨 ∈ ModPred{X = ∣A∣}(ThPred{X = ∣A∣} (V 𝒦)))
  →                 epi 𝔽[ ∣A∣ ] (Lift-Alg 𝑨 (ov α) (ov α))
 𝔽-ModTh-epi-lift A∈ModThK = ∘-epi (𝔽-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi

\end{code}

--------------------------------

<span style="float:left;">[← Varieties.Func.Closure](Varieties.Func.Closure.html)</span>
<span style="float:right;">[Varieties.Func.HSP](Varieties.Func.HSP.html)</span>

{% include UALib.Links.md %}

