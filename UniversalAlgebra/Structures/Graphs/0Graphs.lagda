---
layout: default
title : Structures.Graphs.0Graphs
date : 2021-06-22
author: [agda-algebras development team][]
---

N.B. This module differs from Graphs.lagda in that here we assume some universes are level zero (i.e., ℓ₀). This simplifies some things; e.g., we avoid having to use lift and lower (cf. Graphs.lagda)

Definition [Graph of a structure]. Let 𝑨 be an (𝑅,𝐹)-structure (relations from 𝑅 and operations from 𝐹).
The *graph* of 𝑨 is the structure Gr 𝑨 with the same domain as 𝑨 with relations from 𝑅 and together with a (k+1)-ary relation symbol G 𝑓 for each 𝑓 ∈ 𝐹 of arity k, which is interpreted in Gr 𝑨 as all tuples (t , y) ∈ Aᵏ⁺¹ such that 𝑓 t ≡ y. (See also Definition 2 of https://arxiv.org/pdf/2010.04958v2.pdf)


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Graphs.0Graphs where

open import Agda.Primitive                        using    ( _⊔_    ;   Level )
                                                  renaming ( Set    to  Type
                                                           ; lzero  to ℓ₀     )
open import Agda.Builtin.Equality                 using    ( _≡_    ;   refl  )
open import Data.Sum.Base                         using    ( _⊎_              )
                                                  renaming ( inj₁   to inl
                                                           ; inj₂   to inr    )
open import Data.Product                          using    ( _,_              )
open import Function.Base                         using    ( _∘_              )
import Relation.Binary.PropositionalEquality as PE

-- -- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries   using ( 𝟙 ; ∣_∣ ; ∥_∥ )
open import Structures.Records       using ( signature ; structure )
open import Structures.Examples      using ( Sig∅)
open import Structures.Homs.Records  using ( hom ; is-hom-rel ; is-hom-op)
open import Relations.Continuous     using ( Rel )


open signature
open structure
open _⊎_

Gr-sig : signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀ → signature ℓ₀ ℓ₀

Gr-sig 𝐹 𝑅 = record { symbol = symbol 𝑅 ⊎ symbol 𝐹
                    ; arity  = ar }
 where
 ar : symbol 𝑅 ⊎ symbol 𝐹 → Type ℓ₀
 ar (inl 𝑟) = (arity 𝑅) 𝑟
 ar (inr 𝑓) = (arity 𝐹) 𝑓 ⊎ 𝟙


private variable
 𝐹 𝑅 : signature ℓ₀ ℓ₀

Gr : structure 𝐹 𝑅 {ℓ₀} {ℓ₀} → structure Sig∅ (Gr-sig 𝐹 𝑅) {ℓ₀} {ℓ₀}
Gr {𝐹}{𝑅} 𝑨 = record { carrier = carrier 𝑨 ; op = λ () ; rel = split }
  where
  split : (s : symbol 𝑅 ⊎ symbol 𝐹) → Rel (carrier 𝑨) (arity (Gr-sig 𝐹 𝑅) s) {ℓ₀}
  split (inl 𝑟) arg = rel 𝑨 𝑟 arg
  split (inr 𝑓) args = op 𝑨 𝑓 (args ∘ inl) ≡ args (inr 𝟙.𝟎)


open PE.≡-Reasoning

module _ {𝑨 𝑩 : structure 𝐹 𝑅 {ℓ₀}{ℓ₀}} where

 hom→Grhom : hom 𝑨 𝑩 → hom (Gr 𝑨) (Gr 𝑩)
 hom→Grhom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel (Gr 𝑨) (Gr 𝑩) h
  i (inl 𝑟) a x = ∣ hhom ∣ 𝑟 a x
  i (inr 𝑓) a x = goal
   where
   homop : h (op 𝑨 𝑓 (a ∘ inl)) ≡ op 𝑩 𝑓 (h ∘ (a ∘ inl))
   homop = ∥ hhom ∥ 𝑓 (a ∘ inl)

   goal : op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡ h (a (inr 𝟙.𝟎))
   goal = op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡⟨ PE.sym homop ⟩
          h (op 𝑨 𝑓 (a ∘ inl))   ≡⟨ PE.cong h x ⟩
          h (a (inr 𝟙.𝟎))         ∎

  ii : is-hom-op (Gr 𝑨) (Gr 𝑩) h
  ii = λ ()


 Grhom→hom : hom (Gr 𝑨) (Gr 𝑩) → hom 𝑨 𝑩
 Grhom→hom (h , hhom) = h , (i , ii)
  where
  i : is-hom-rel 𝑨 𝑩 h
  i R a x = ∣ hhom ∣ (inl R) a x
  ii : is-hom-op 𝑨 𝑩 h
  ii f a = goal
   where
   split : arity 𝐹 f ⊎ 𝟙 → carrier 𝑨
   split (inl x) = a x
   split (inr y) = op 𝑨 f a
   goal : h (op 𝑨 f a) ≡ op 𝑩 f (λ x → h (a x))
   goal = PE.sym (∣ hhom ∣ (inr f) split refl)

\end{code}

{- Lemma III.1. Let S be a signature and A be an S-structure.
Let Σ be a finite set of identities such that A ⊧ Σ. For every
instance X of CSP(A), one can compute in polynomial time an
instance Y of CSP(A) such that Y ⊧ Σ and | Hom(X , A)| = |Hom(Y , A)|. -}


\begin{code}

record _⇛_⇚_ (𝑩 𝑨 𝑪 : structure 𝐹 𝑅) : Type ℓ₀ where
 field
  to   : hom 𝑩 𝑨 → hom 𝑪 𝑨
  from : hom 𝑪 𝑨 → hom 𝑩 𝑨
  to∼from : ∀ h → (to ∘ from) h ≡ h
  from∼to : ∀ h → (from ∘ to) h ≡ h

module _ {χ : Level}{X : Type χ}
         {𝑨 : structure 𝐹 𝑅 {ℓ₀} {ℓ₀}} where


 -- LEMMAIII1 : (ℰ : Pred (Term X × Term X) (ℓ₀ ⊔ χ))
 --  →          (𝑨 ∈ Mod ℰ)
 --  →          ∀(𝑩 : structure 𝐹 𝑅)
 --  →          Σ[ 𝑪 ∈ structure 𝐹 𝑅 ] (𝑪 ∈ Mod ℰ × (𝑩 ⇛ 𝑨 ⇚ 𝑪))
 -- LEMMAIII1 ℰ 𝑨⊧ℰ 𝑩 = {!!} , {!!}

 -- LEMMAIII1 : {n : ℕ}(ℰ : Fin n → (Term X × Term X))
 --  →          (𝑨 ∈ fMod ℰ)
 --  →          ∀(𝑩 : structure 𝐹 𝑅)
 --  →          Σ[ 𝑪 ∈ structure 𝐹 𝑅 ] (𝑪 ∈ fMod ℰ × (𝑩 ⇛ 𝑨 ⇚ 𝑪))
 -- LEMMAIII1 ℰ 𝑨⊧ℰ 𝑩 = {!!} , {!!}

\end{code}


------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

