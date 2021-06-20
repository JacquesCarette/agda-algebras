---
layout: default
title : Structures.congruences module
date : 2021-05-28
author: William DeMeo
---


#### Congruences for structures as records

This module is similar to Congruences.lagda but for structures represented using records rather than
dependent pair type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Structures.AsRecords

open import Structures.AsRecords

module Structures.congruences {𝑅 𝐹 : signature} where

open import Agda.Builtin.Equality  using    ( _≡_   ;  refl     )
open import Agda.Primitive         using    (  _⊔_  ;  lsuc     )
                                   renaming (  Set  to Type     )
open import Data.Product           using    (  _,_  ;  Σ
                                            ;  _×_  ;  Σ-syntax )
                                   renaming ( proj₁ to fst      )
open import Level                  using    ( Level ;  Lift
                                            ; lift  ;  lower    )
                                   renaming ( zero  to ℓ₀
                                            ; suc   to lsuc     )
open import Function.Base          using    ( _∘_               )
open import Relation.Unary         using    ( _∈_   ;  Pred     )
open import Relation.Binary        using    ( IsEquivalence     )
                                   renaming ( Rel   to BinRel   )



open import Overture.Preliminaries   using ( ∣_∣ )
open import Relations.Discrete       using ( _|:_ ; 0[_])
open import Relations.Quotients      using ( Equivalence ; 0[_]Equivalence ; Quotient
                                           ; ⟪_⟫ ; ⌞_⌟ ; ⟪_∼_⟫-elim ; _/_ )
open import Relations.Extensionality using ( swelldef )


private variable α ρ : Level

con : (𝑨 : structure {α} {ρ} 𝑅 𝐹) → Type (lsuc α ⊔ lsuc ρ)
con {α}{ρ} 𝑨 = Σ[ θ ∈ Equivalence (carrier 𝑨) {α ⊔ ρ}] (compatible 𝑨 ∣ θ ∣)

-- Example. The zero congruence of a structure.
0[_]compatible : (𝑨 : structure {α} {ρ} 𝑅 𝐹) → swelldef ℓ₀ α → (𝑓 : symbol 𝐹) → (op 𝑨) 𝑓 |: (0[ carrier 𝑨 ] {ρ})
0[ 𝑨 ]compatible wd 𝑓 {i}{j} ptws0  = lift γ
  where
  γ : ((op 𝑨) 𝑓) i ≡ ((op 𝑨) 𝑓) j
  γ = wd ((op 𝑨) 𝑓) i j (lower ∘ ptws0)

0con[_] : (𝑨 : structure {α} {ρ} 𝑅 𝐹) → swelldef ℓ₀ α → con 𝑨
0con[ 𝑨 ] wd = 0[ carrier 𝑨 ]Equivalence , 0[ 𝑨 ]compatible wd

-- Quotient structures

quotient : (𝑨 : structure {α} {ρ} 𝑅 𝐹) → con 𝑨 → structure {lsuc (α ⊔ ρ)} {ρ} 𝑅 𝐹
quotient {α}{ρ}𝑨 θ = record
                     { carrier = Quotient (carrier 𝑨) ∣ θ ∣     -- domain of quotient structure
                     ; rel = λ r x → ((rel 𝑨) r) (λ i → ⌞ x i ⌟)   -- interpretation of relations
                     ; op = λ f b → ⟪ ((op 𝑨) f) (λ i → ⌞ b i ⌟) ⟫ {fst ∣ θ ∣} -- interp of operations
                     }

-- Alternative notation for the quotient (useful on when the levels can be inferred).
_╱_ : (𝑨 : structure {α} {ρ} 𝑅 𝐹) → con 𝑨 → structure {lsuc (α ⊔ ρ)} {ρ} 𝑅 𝐹
_╱_ = quotient


/≡-elim : {𝑨 : structure {α} {ρ} 𝑅 𝐹}( (θ , _ ) : con 𝑨){u v : carrier 𝑨}
 →        ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ {∣ θ ∣} → ∣ θ ∣ u v
/≡-elim θ {u}{v} x =  ⟪ u ∼ v ⟫-elim{R = ∣ θ ∣} x


-- Example. The zero congruence of a quotient structure.
𝟎[_╱_] : (𝑨 : structure {α} {ρ} 𝑅 𝐹)(θ : con 𝑨) → swelldef ℓ₀ (lsuc α ⊔ lsuc ρ)  → con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] wd = 0con[ 𝑨 ╱ θ ] wd

\end{code}


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------











-- 𝟘[_╱_] : (𝑨 : structure {α} 𝑅 {ρ} 𝐹)(θ : con 𝑨) → BinRel (_/_ {α}{ρ} (carrier 𝑨) ∣ θ ∣) (lsuc (α ⊔ ρ))
-- 𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v






<!-- NO LONGER NEEDED ----------------------------------------------------------

-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Agda.Builtin.Equality using (_≡_; refl)
-- open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Unary using (Pred; _∈_)
-- open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)

-- -- Imports from the Agda carrierersal Algebra Library
-- open import Algebras.Basic
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; ∣_∣; ∥_∥; fst)
-- open import Relations.Discrete using (𝟎; _|:_)
-- open import Relations.Quotients using (_/_; ⟪_⟫)

--------------------------------------------------------------------------------- -->
open _/ₜ_

_╱ₜ_ : (𝑩 : Structure 𝑅 𝐹 {β}) → Con{α} 𝑩 → Structure 𝑅 𝐹

𝑩 ╱ₜ θ = (∣ 𝑩 ∣ /ₜ ∣ fst θ ∣)                                    -- domain of the quotient algebra
, rel -- basic relations of the quotient structure
, op        -- basic operations of the quotient algebra
where
rel : (r : ∣ 𝑅 ∣)(b : ∥ 𝑅 ∥ r → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣) → Type ?
rel r b = ?
-- (λ 𝑟 [ x ] → ((𝑟 ʳ 𝑩) λ i → ∣ fst θ ∣ (x i)))
op : (f : ∣ 𝐹 ∣)(b : ∥ 𝐹 ∥ f → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣) → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣
op f b = ? -- λ 𝑓 [ 𝑎 ] → [ ((𝑓 ᵒ 𝑩)(λ i →  𝑎 i)) ]  

record IsMinBin {A : Type α} (_≣_ : BinRel A ℓ₀ ) : Typeω where
 field
   isequiv : IsEquivalence{α}{ℓ₀} _≣_
   ismin : {ρ' : Level}(_≋_ : BinRel A ρ'){x y : A} → x ≣ y → x ≋ y

 reflexive : _≡_ ⇒ _≣_
 reflexive refl = IsEquivalence.refl isequiv

 corefl : _≣_ ⇒ _≡_
 corefl x≣y = ismin _≡_ x≣y

