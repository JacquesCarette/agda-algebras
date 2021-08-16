---
layout: default
title : Homomorphisms.Setoid.Noether module (The Agda Universal Algebra Library)
date : 2021-07-17
author: [agda-algebras development team][]
---

### Homomorphism Theorems

This is the [Homomorphisms.Setoid.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Level using ( Level )
open import Algebras.Basic

module Homomorphisms.Setoid.Noether {𝑆 : Signature 𝓞 𝓥} where

\end{code}


#### Homomorphism Decomposition for SetoidAlgebras


If `τ : hom 𝑨 𝑩`, `ν : hom 𝑨 𝑪`, `ν` is surjective, and `ker ν ⊆ ker τ`, then there exists `φ : hom 𝑪 𝑩` such that `τ = φ ∘ ν` so the following diagram commutes:

```
𝑨 --- ν ->> 𝑪
 \         .
  \       .
   τ     φ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

module _ {α ρᵃ : Level} {𝑨 : SetoidAlgebra α ρᵃ}
         {β ρᵇ : Level} (𝑩 : SetoidAlgebra β ρᵇ)
         {γ ρᶜ : Level} {𝑪 : SetoidAlgebra γ ρᶜ} where

 private
  A = 𝕌[ 𝑨 ]
  B = 𝕌[ 𝑩 ]
  C = 𝕌[ 𝑪 ]

 open import Axiom.Extensionality.Propositional    using    ()
                                                  renaming (Extensionality to funext)

 HomFactor : swelldef 𝓥 γ
  →          (τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →          kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣ → IsSurjective ∣ ν ∣
             --------------------------------------------------
  →          Σ[ φ ∈ (hom 𝑪 𝑩)] (∣ τ ∣ ≈ ∣ φ ∣ ∘ ∣ ν ∣)

 HomFactor wd τ ν Kντ νE = (φ , φIsHomCB)  , τφν
  where
  νInv : C → A
  νInv = SurjInv ∣ ν ∣ νE

  η : ∀ c → c ≡ ∣ ν ∣ (νInv c)
  η c = sym (SurjInvIsRightInv ∣ ν ∣ νE c)

  φ : C → B
  φ = ∣ τ ∣ ∘ νInv

  ξ : ∀ a → kernel ∣ ν ∣ (a , νInv (∣ ν ∣ a))
  ξ a = η (∣ ν ∣ a)

  τφν : ∣ τ ∣ ≈ φ ∘ ∣ ν ∣
  τφν x = Kντ (ξ x)

  φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
  φIsHomCB 𝑓 c =
   φ ((𝑓 ̂ 𝑪) c)                    ≡⟨ ≡-cong φ (wd (𝑓 ̂ 𝑪) c (∣ ν ∣ ∘ (νInv ∘ c)) λ i → η ((c i)))⟩
   φ ((𝑓 ̂ 𝑪)(∣ ν ∣ ∘(νInv ∘ c)))   ≡⟨ ≡-cong φ (∥ ν ∥ 𝑓 (νInv ∘ c))⁻¹ ⟩
   φ (∣ ν ∣((𝑓 ̂ 𝑨)(νInv ∘ c)))     ≡⟨ sym (τφν ((𝑓 ̂ 𝑨)(νInv ∘ c))) ⟩
   ∣ τ ∣((𝑓 ̂ 𝑨)(νInv ∘ c))         ≡⟨ ∥ τ ∥ 𝑓 (νInv ∘ c) ⟩
   (𝑓 ̂ 𝑩)(λ x → ∣ τ ∣(νInv (c x))) ∎

\end{code}

If, in addition to the hypotheses of the last theorem, we assume τ is epic, then so is φ. (Note that the proof also requires an additional local function extensionality postulate, `funext β β`.)

\begin{code}

 open epi
 HomFactorEpi : swelldef 𝓥 γ
  →             (τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →             kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣
  →             IsSurjective ∣ ν ∣ → IsSurjective ∣ τ ∣
                ---------------------------------------------
  →             Σ[ φ ∈ epi 𝑪 𝑩 ] ∣ τ ∣ ≈ (φ .map) ∘ ∣ ν ∣

 HomFactorEpi wd τ ν kerincl νe τe = record { map = fst ∣ φF ∣
                                            ; is-epi = (snd ∣ φF ∣) , φE
                                            } , ∥ φF ∥
  where
   φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∣ τ ∣ ≈ ∣ φ ∣ ∘ ∣ ν ∣
   φF = HomFactor wd τ ν kerincl νe

   φ : C → B
   φ = ∣ τ ∣ ∘ (SurjInv ∣ ν ∣ νe)

   φE : IsSurjective φ
   φE = epic-factor  ∣ τ ∣ ∣ ν ∣ φ ∥ φF ∥ τe

\end{code}

--------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
