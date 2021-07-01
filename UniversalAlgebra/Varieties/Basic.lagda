---
layout: default
title : Varieties.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

## Varieties, Model Theory, and Equational Logic

This section presents the [Varieties.Basic][] module of the [Agda Universal Algebra Library][] where the binary "models" relation ⊧, relating algebras (or classes of algebras) to the identities that they satisfy, is defined.

Agda supports the definition of infix operations and relations, and we use this to define ⊧ so that we may write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊫ p ≈ q`.



**Notation**. In the [Agda UniversalAlgebra][] library, because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations ⊧ and ≈. As a reasonable alternative to what we would normally express informally as 𝒦 ⊧ 𝑝 ≈ 𝑞, we have settled on 𝒦 ⊫ p ≈ q to denote this relation.  To reiterate, if 𝒦 is a class of 𝑆-algebras, we write 𝒦 ⊧ 𝑝 ≋ 𝑞 if every 𝑨 ∈ 𝒦 satisfies 𝑨 ⊧ 𝑝 ≈ 𝑞.

**Unicode Hints**. To produce the symbols ≈, ⊧, and ≋ in [agda2-mode][], type `\~~`, `\models`, and `\~~~`, respectively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level using ( Level )
open import Algebras.Basic

module Varieties.Basic {𝑆 : Signature 𝓞 𝓥} where


-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Primitive          using    ( _⊔_ ;  lsuc )
                                    renaming ( Set to Type )
open import Data.Product            using    ( _×_ ; _,_ ; Σ-syntax)
                                    renaming ( proj₁ to fst
                                             ; proj₂ to snd )
open import Relation.Unary          using    ( Pred ; _∈_ )



-- -- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries    using ( _≈_ )
open import Algebras.Products {𝑆 = 𝑆} using ( ov )
open import Terms.Basic       {𝑆 = 𝑆} using ( Term ; 𝑻 ; lift-hom )
open import Terms.Operations  {𝑆 = 𝑆} using ( _⟦_⟧ )

private variable χ α ρ ι : Level
                 X : Type χ

\end{code}


### The "models" relation
We define the binary "models" relation ⊧ using infix syntax so that we may
write, e.g., `𝑨 ⊧ p ≈ q` or `𝒦 ⊫ p ≈ q`, relating algebras (or classes of
algebras) to the identities that they satisfy. We also prove a couple of useful
facts about ⊧.  More will be proved about ⊧ in the next module,
Varieties.EquationalLogic.

\begin{code}

_⊧_≈_ : Algebra α 𝑆 → Term X → Term X → Type _
𝑨 ⊧ p ≈ q = 𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧

_⊫_≈_ : Pred(Algebra α 𝑆) ρ → Term X → Term X → Type _
𝒦 ⊫ p ≈ q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}

The expression `𝑨 ⊧ p ≈ q` represents the assertion that the identity `p ≈ q`
holds when interpreted in the algebra `𝑨`; syntactically, `𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧`.

The expression `𝑨 ⟦ p ⟧ ≈ 𝑨 ⟦ q ⟧` denotes *extensional equality*; that is,
for each "environment" `η :  X → ∣ 𝑨 ∣` (assigning values in the domain of `𝑨`
to the variable symbols in `X`) the (intensional) equality `𝑨 ⟦ p ⟧ η ≡ 𝑨 ⟦ q ⟧ η`
holds.


### Equational theories and models

If 𝒦 denotes a class of structures, then `Th 𝒦` represents the set of identities
modeled by the members of 𝒦.

\begin{code}

Th : Pred (Algebra α 𝑆) (ov α) → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

\end{code}

Perhaps we want to represent Th 𝒦 as an indexed collection.  We do so
essentially by taking `Th 𝒦` itself to be the index set, as follows.

\begin{code}

module _ {X : Type χ}{𝒦 : Pred (Algebra α 𝑆) (ov α)} where

 ℐ : Type (ov(α ⊔ χ))
 ℐ = Σ[ (p , q) ∈ (Term X × Term X) ] 𝒦 ⊫ p ≈ q

 ℰ : ℐ → Term X × Term X
 ℰ ((p , q) , _) = (p , q)


\end{code}

If `ℰ` denotes a set of identities, then `Mod ℰ` is the class of structures
satisfying the identities in `ℰ`.

\begin{code}

Mod : Pred(Term X × Term X) (ov α) → Pred(Algebra α 𝑆) _
Mod ℰ = λ 𝑨 → ∀ p q → (p , q) ∈ ℰ → 𝑨 ⊧ p ≈ q
-- (tupled version)
Modᵗ : {I : Type ι} → (I → Term X × Term X) → {α : Level} → Pred(Algebra α 𝑆) _
Modᵗ ℰ = λ 𝑨 → ∀ i → 𝑨 ⊧ (fst (ℰ i)) ≈ (snd (ℰ i))

\end{code}

-------------------------------------

[↑ Varieties](Varieties.html)
<span style="float:right;">[Varieties.EquationalLogic →](Varieties.EquationalLogic.html)</span>

{% include UALib.Links.md %}


--------------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team














<!--

  -- open import Relation.Binary.Core using (_⇔_)

  -- ⊧-H : DFunExt → {p q : Term X} → 𝒦 ⊫ p ≈ q ⇔ (∀ 𝑨 φ → 𝑨 ∈ 𝒦 → ∣ φ ∣ ∘ (𝑻 X ⟦ p ⟧) ≡ ∣ φ ∣ ∘(𝑻 X ⟦ q ⟧))
  -- ⊧-H fe {p}{q} = ⊧-H-class-invar fe {p}{q} , ⊧-H-class-coinvar fe {p}{q}


-->
Soundness of the inference rules. We assume a model 𝑨 that validates all equations in ℰ.


\begin{code}

-- module Soundness {ι : Level}{I : Type ι}
--                  {χ : Level}(ℰ : {X : Type χ} → I → Term X × Term X)
--                  {α : Level}(𝑨 : Algebra α 𝑆)
--                  (Amod : 𝑨 ∈ Modtup ℰ) where

--  -- In any 𝑨 ∈ Mod ℰ, derived equality is actual equality.

--  sound : {X : Type χ}{p q : Term X} → ℰ ⊢ X ▹ p ≈ q → 𝑨 ⊧ p ≈ q
--  sound x = {!!}

\end{code}
 -- (hyp i)                        =  V i
 --    sound (app {op = op} es) ρ           =  den .cong (refl , λ i → sound (es i) ρ)
 --    sound (sub {t = t} {t' = t'} e σ) ρ  =  begin
 --      ⦅ t [ σ ]   ⦆ .apply ρ   ≈⟨ substitution {M = M} t σ ρ ⟩
 --      ⦅ t         ⦆ .apply ρ'  ≈⟨ sound e ρ' ⟩
 --      ⦅ t'        ⦆ .apply ρ'  ≈˘⟨ substitution {M = M} t' σ ρ ⟩
 --      ⦅ t' [ σ ]  ⦆ .apply ρ   ∎
 --      where
 --      open SetoidReasoning Den
 --      ρ' = ⦅ σ ⦆s ρ

 --    sound (base x {f} {f'})              =  isEquiv {M = M} .IsEquivalence.refl {var' x λ()}

 --    sound (refl t)                       =  isEquiv {M = M} .IsEquivalence.refl {t}
 --    sound (sym {t = t} {t' = t'} e)      =  isEquiv {M = M} .IsEquivalence.sym
 --                                            {x = t} {y = t'} (sound e)
 --    sound (trans  {t₁ = t₁} {t₂ = t₂}
 --                  {t₃ = t₃} e e')        =  isEquiv {M = M} .IsEquivalence.trans
 --                                            {i = t₁} {j = t₂} {k = t₃} (sound e) (sound e')



