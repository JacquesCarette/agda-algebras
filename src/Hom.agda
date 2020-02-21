--File: Hom.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 21 Feb 2020

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
  using (Level; ∃; _,_; ∣_∣; _≡_; refl; _∘_; Pred)
open import Basic

module Hom where

private
  variable
    i j k : Level
    S : Signature i j

--The category of algebras Alg with morphisms as Homs

Hom : Algebra k S -> Algebra k S -> Set _
Hom {S = 𝐹 , ρ} (A , 𝐹ᴬ) (B , 𝐹ᴮ) =
    ∃ λ (f : A -> B) -> (𝓸 : 𝐹) (𝒂 : ρ 𝓸 -> A)
     -----------------------------------------
      ->    f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂)

id : (𝑨 : Algebra k S) -> Hom 𝑨 𝑨
id (A , 𝑨) = (λ x -> x) , λ _ _ -> refl

private
  variable
    𝑨 𝑩 : Algebra k S

_>>>_ : {𝑪 : Algebra k S}

  ->   Hom 𝑨 𝑩  ->  Hom 𝑩 𝑪
      -------------------------
  ->         Hom 𝑨 𝑪

_>>>_ {S = 𝐹 , ρ} {𝑨 = (A , 𝐹ᴬ)} {𝑪 = (C , 𝐹ᶜ)}
      (f , α) (g , β) = g ∘ f , γ
        where
          γ :    (𝓸 : 𝐹) (𝒂 : ρ 𝓸 -> A)
               ---------------------------------------
            ->   (g ∘ f) (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᶜ 𝓸 (g ∘ f ∘ 𝒂)
          γ 𝓸 𝒂 rewrite α 𝓸 𝒂 = β 𝓸 (f ∘ 𝒂)

-- Equalizers in Alg
_~_ : Hom 𝑨 𝑩 → Hom 𝑨 𝑩 → Pred ∣ 𝑨 ∣ _
_~_ (f , _) (g , _) x = f x ≡ g x
