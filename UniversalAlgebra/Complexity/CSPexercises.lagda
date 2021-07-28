---
layout: default
title : Complexity.CSPexercises module (The Agda Universal Algebra Library)
date : 2021-07-26
author: [agda-algebras development team][] and Libor Barto⁺
---

⁺All excercises below were made by Libor Barto (for students at Charles University), and formalized in MLTT/Agda by the [agda-algebras development team][].

### CSP Exercises

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Complexity.CSPexercises  where


open import Agda.Primitive        using ( _⊔_ ; Level ) renaming ( Set to Type ; lzero to ℓ₀ )
open import Agda.Builtin.Equality using ( _≡_ ; refl )
open import Data.Product          using ( _,_ ; _×_ ; Σ-syntax )
open import Data.Sum.Base         using ( _⊎_ ) renaming ( inj₁ to inl ; inj₂ to inr )
open import Data.Fin.Base         using ( Fin )
open import Data.Nat              using ( ℕ )
open import Function.Base         using ( _∘_ )
open import Relation.Nullary      using ( ¬_ )
open import Relation.Unary        using ( Pred ; _∈_ ; _∉_ )
import Relation.Binary.PropositionalEquality as PE

-- -- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries using ( 𝟙 ; ∣_∣ ; ∥_∥ )
open import Overture.Preliminaries using ( 𝟘 ; 𝟙 ; 𝟚 ; 𝟛 )
open import Relations.Continuous   using ( Rel )
open import Structures.Basic       using ( signature ; structure )
open import Structures.Examples    using ( S∅ ; S001 ; S021)
open import Structures.Homs        using ( hom ; is-hom-rel ; is-hom-op )
open import Structures.Terms.Basic using ( Term )

open signature
open structure
open _⊎_



\end{code}


Some exercises below refer to the following relations on 𝟚 := \{0, 1\} (where i, j ∈ 𝟚):

\begin{align*}
 C_i    & := \{ i \}                             \\
 R      & := \{ (0, 0), (1, 1) \}                 \\
 N      & := \{ (0, 1), (1, 0) \}                  \\
 S_{ij} & := 𝟚² - \{ (i , j) \},                    \\
 H      & := 𝟚³ - \{ (1, 1, 0) \}                    \\
 G_1    & := \{ (0,0,0), (0,1,1), (1,0,1), (1,1,0) \} \\
 G_2    & := \{ (0,0,1), (0,1,0), (1,0,0), (1,1,1) \}
\end{align*}


**Exercise 1**. Prove that the definitions of CSP(𝔸) (satisfiability of a list of constraints, homomorphism   problem, truth of primitive positive formulas) are equivalent.


**Exercise 2**. Find a polymomial-time algorithm for CSP(A), where

2.1. 𝑨 = ({0, 1}, 𝑅) = (𝟚 , \{(0,0), (1, 1)\})
2.2. 𝑨 = ({0, 1}, 𝑅, 𝐶₀, 𝐶₁) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ 0 \} , \{ 1 \})
2.3. 𝑨 = ({0, 1}, 𝑆₁₀) = (𝟚 , 𝟚³ - \{ (1, 0) \})
2.4. 𝑨 = ({0, 1}, 𝑆₁₀, 𝐶₀, 𝐶₁) = (𝟚 , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
2.5. 𝑨 = ({0, 1}, 𝑆₀₁, 𝑆₁₀, 𝐶₀, 𝐶₁) = (𝟚 , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
2.6. 𝑨 = ({0, 1}, 𝑁) = (𝟚 , \{ (0, 1) , (1, 0) \})
2.7. 𝑨 = ({0, 1}, 𝑅, 𝑁, 𝐶₀, 𝐶₁) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \})
2.8. 𝑨 = ({0, 1}, 𝑅, 𝑁, 𝐶₀, 𝐶₁, 𝑆₀₀, 𝑆₀₁, 𝑆₁₀, 𝑆₁₁) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \} , 𝟚³ - \{ (0, 0) \} , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , 𝟚³ - \{ (1, 1) \})
2.9. 𝑨 = ({0, 1}, all unary and binary relations)



**Solution 2.1**. If 𝑨 = ({0, 1}, Rᵃ) = (𝟚 , \{(0,0), (1, 1)\}), then an instance of (the HOM
formulation of) CSP(𝑨) is a relational structure 𝑩 = (B, Rᵇ⟩, where Rᵇ ⊆ B² and we must decide
whether there exists a homomorphism f : 𝑩 → 𝑨, that is, a map f : B → A (= 𝟚) such that
∀ (b, b'), if (b, b') ∈ Rᵇ, then (f b, f b') ∈ Rᵃ.

Of course, the constant map f ≡ 0 that sends every element of B to 0 (as well as the
constantly-1 map) is such a homomorphism.  Let's prove this formally.

\begin{code}
module solution-2-1 where

 -- The (purely) relational structure with
 -- + 2-element domain,
 -- + one binary relation Rᵃ := \{(0,0), (1, 1)\}

 data Rᵃ : Pred (𝟚 × 𝟚) ℓ₀ where
  r1 : (𝟚.𝟎 , 𝟚.𝟎 ) ∈ Rᵃ
  r2 : (𝟚.𝟏 , 𝟚.𝟏 ) ∈ Rᵃ

 𝑨 : structure S∅    -- (no operation symbols)
               S001  -- (one binary relation symbol)

 𝑨 = record { carrier = 𝟚
            ; op = λ ()
            ; rel = λ _ x → ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵃ
            }


 -- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.
 claim : (𝑩 : structure {ℓ₀}{ℓ₀}{ℓ₀}{ℓ₀} S∅ S001 {ℓ₀}{ℓ₀}) → hom 𝑩 𝑨
 claim 𝑩 = (λ x → 𝟚.𝟎) , (λ _ _ _ → r1) , λ ()

\end{code}

In general, whenever the template structure 𝑨 has a one-element subuniverse, say, \{ a \},
then the constant map that always gives a is a homomorphism from any structure in the given
signature to 𝑨. ∎



**Solution 2.2**. If 𝑨 = (\{ 0, 1 \}, Rᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0, 0) , (1, 1) \} , \{ 0 \} , \{ 1 \}),
then an instance of HOM CSP(𝑨) is a relational structure 𝑩 = (B, Rᵇ, C₀ᵇ, C₁ᵇ), where
Rᵇ ⊆ B², C₀ᵇ ⊆ B, C₁ᵇ ⊆ B, and we must decide whether there exists a homomorphism
f : hom 𝑩 𝑨, that is, a map f : B → 𝟚 such that the following conditions hold:
 1. ∀ (x, y) ∈ B², (x, y) ∈ Rᵇ implies (f x , f y) ∈ 𝑅,
 2. f is constantly 0 on C₀ᵇ, and
 3. f is constantly 1 on C₁ᵇ.

The first condition says that if (x, y) ∈ Rᵇ, then either f x = 0 = f y or f x = 1 = f y.

Therefore, there exists a homomorphism f : hom 𝑩 𝑨 iff Rᵇ ∩ C₀ᵇ × C₁ᵇ = ∅ = Rᵇ ∩ C₁ᵇ × C₀ᵇ.

We can check this in polynomial time (in the size of the input instance 𝑩) since we just need
to check each pair (x, y) ∈ Rᵇ and make sure that the following two implications hold:

 1.  x ∈ C₀ᵇ  only if  y ∉ C₁ᵇ, and
 2.  x ∈ C₁ᵇ  only if  y ∉ C₀ᵇ.

\begin{code}

module solution-2-2 where

 -- The (purely) relational structure with
 -- + 2-element domain,
 -- + one binary relation: Rᵃ := { (0,0), (1, 1) }
 -- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }

 data Rᵃ : Pred (𝟚 × 𝟚) ℓ₀ where
  r1 : (𝟚.𝟎 , 𝟚.𝟎 ) ∈ Rᵃ
  r2 : (𝟚.𝟏 , 𝟚.𝟏 ) ∈ Rᵃ

 data C₀ᵃ : Pred 𝟚 ℓ₀ where
  c₀ : 𝟚.𝟎 ∈ C₀ᵃ

 data C₁ᵃ : Pred 𝟚 ℓ₀ where
  c₁ : 𝟚.𝟏 ∈ C₁ᵃ


 𝑨 : structure S∅    -- (no operation symbols)
               S021  -- (one binary relation symbol)

 𝑨 = record { carrier = 𝟚
            ; op = λ ()
            ; rel = rels
            }
            where
            rels : (r : 𝟛) → Rel 𝟚 (arity S021 r)
            rels 𝟛.𝟎 x = ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵃ
            rels 𝟛.𝟏 x = x 𝟙.𝟎 ∈ C₀ᵃ
            rels 𝟛.𝟐 x = x 𝟙.𝟎 ∈ C₁ᵃ


 -- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig-2, we can construct a homomorphism from 𝑩 to 𝑨.
 claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})
  →       (∀ (x : 𝟚 → carrier 𝑩)
           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...
           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))
             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))
          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))
          )
  →       hom 𝑩 𝑨
 claim 𝑩 x = {!!}

\end{code}

**Solution 2.3**. 𝑨 = ({0, 1}, 𝑆₁₀) = (𝟚 , 𝟚³ - \{ (1, 0) \})
\begin{code}

\end{code}

**Solution 2.4**. 𝑨 = ({0, 1}, 𝑆₁₀, 𝐶₀, 𝐶₁) = (𝟚 , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
\begin{code}

\end{code}

**Solution 2.5**. 𝑨 = ({0, 1}, 𝑆₀₁, 𝑆₁₀, 𝐶₀, 𝐶₁) = (𝟚 , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
\begin{code}

\end{code}

**Solution 2.6**. 𝑨 = ({0, 1}, 𝑁) = (𝟚 , \{ (0, 1) , (1, 0) \})
\begin{code}

\end{code}

**Solution 2.7**. 𝑨 = ({0, 1}, 𝑅, 𝑁, 𝐶₀, 𝐶₁) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \})
\begin{code}

\end{code}

**Solution 2.8**. 𝑨 = ({0, 1}, 𝑅, 𝑁, 𝐶₀, 𝐶₁, 𝑆₀₀, 𝑆₀₁, 𝑆₁₀, 𝑆₁₁) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \} , 𝟚³ - \{ (0, 0) \} , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , 𝟚³ - \{ (1, 1) \})
\begin{code}

\end{code}

**Solution 2.9**. 𝑨 = ({0, 1}, all unary and binary relations)


**Exercise 3**. Find a polynomial-time algorithm for CSP({0, 1}, 𝐻, 𝐶₀, 𝐶₁).

**Exercise 4**. Find a polynomial-time algorithm for CSP({0, 1}, 𝐶₀, 𝐶₁, 𝐺₁, 𝐺₂).

**Exercise 5**. Find a polynomial-time algorithm for CSP(ℚ, <).



