---
layout: default
title : Varieties.EquationalLogic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [the ualib/agda-algebras development team][]
---

This is the [Varieties.EquationalLogic][] module of the [Agda Universal Algebra Library][].

### Entailment, derivation rules, soundness and completeness

This module is based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem.
(See: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import Level using ( Level )
open import Algebras.Basic

module Varieties.EquationalLogic {𝑆 : Signature 𝓞 𝓥} where


-- imports from Agda and the Agda Standard Library -------------------------------------------
open import Agda.Builtin.Equality  using    ( _≡_                      )
                                   renaming ( refl    to ≡-refl        )
open import Agda.Primitive         using    ( _⊔_     ;  lsuc          )
                                   renaming ( Set     to Type          )
open import Data.Product           using    ( _,_     ;  Σ-syntax )
open import Function.Bundles       using    ( Func                     )
open import Relation.Binary        using    ( Setoid  ;  IsEquivalence )
open import Relation.Unary          using    ( Pred ; _∈_ )
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Setoid        using    ( Carrier ; _≈_ ; isEquivalence )
open Func          renaming ( f     to  apply )
open IsEquivalence renaming ( refl  to  reflE
                            ; sym   to  symmE
                            ; trans to  tranE )


-- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries       using ( ∣_∣ )
open import Algebras.Setoid      {𝑆 = 𝑆} using ( SetoidAlgebra ; ⟦_⟧s )
open import Algebras.Products    {𝑆 = 𝑆} using ( ov )
open import Terms.Basic          {𝑆 = 𝑆} using ( Term )
open import Terms.Setoid         {𝑆 = 𝑆} using ( module Environment ; Ops ; Sub ; _[_] )

open Term

private variable
 χ α ρ ℓ : Level
 X Γ Δ : Type χ
 f     : ∣ 𝑆 ∣
 op    : ∣ Ops Γ ∣

-- Equations
-- An equation is a pair (s , t) of terms of the same sort in the same context.
record Eq : Type (ov χ) where
 constructor _≐_
 field
  {cxt} : Type χ
  lhs   : Term cxt
  rhs   : Term cxt

open Eq


-- Equation p ≐ q holding in algebra M.
_⊨_ : (M : SetoidAlgebra α ℓ)(tid : Eq{χ}) → Type _
M ⊨ (p ≐ q) = Equal p q                                -- (type \|= to get ⊨)
 where open Environment M

module _ {ι : Level}{I : Type ι} where

 -- Sets of equations are presented as collection E : I → Eq.
 -- Here's is how we represent the assertion that an algebra
 -- models all equations in a set E.
 _⊧_ : (𝑨 : SetoidAlgebra α ρ)(E : I → Eq{χ}) → Type _
 𝑨 ⊧ E = ∀ i → Equal (lhs (E i))(rhs (E i))       -- (type \models to get ⊧)
  where open Environment 𝑨

 -- tupled version
 Mod : (I → Eq{χ}) → Pred(SetoidAlgebra α ρ) (χ ⊔ ι ⊔ α ⊔ ρ)
 Mod E = λ 𝑨 → 𝑨 ⊧ E

_⊫_ : Pred (SetoidAlgebra α ρ) ρ → Eq{χ} → Type _
𝒦 ⊫ eq = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊨ eq                        -- (type \||= to get ⊫)



module _ {α}{ρ}{ι}{I : Type ι} where
 -- An entailment E ⊃ eq holds iff it holds in all models of E.
 _⊃_ : (E : I → Eq{χ}) (eq : Eq{χ}) → Type _
 E ⊃ eq = (M : SetoidAlgebra α ρ) → M ⊧ E → M ⊨ eq

\end{code}


#### Derivations in a context

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)

\begin{code}

module _ {χ ι : Level} where

 data _⊢_▹_≈_ {I : Type ι}
  (E : I → Eq) : (Γ : Type χ) (p q : Term Γ) → Type ((ov χ) ⊔ ι) where

  hyp : ∀ i → let p ≐ q = E i in E ⊢ _ ▹ p ≈ q

  app : ∀ {ps qs} → (∀ i → E ⊢ Γ ▹ ps i ≈ qs i) → E ⊢ Γ ▹ (node f ps) ≈ (node f qs)

  sub : ∀ {p q} → E ⊢ Δ ▹ p ≈ q → ∀ (σ : Sub Γ Δ) → E ⊢ Γ ▹ (p [ σ ]) ≈ (q [ σ ])

  refl : ∀ {p} → E ⊢ Γ ▹ p ≈ p

  sym : ∀ {p q : Term Γ} → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ p

  trans : ∀ {p q r : Term Γ} → E ⊢ Γ ▹ p ≈ q → E ⊢ Γ ▹ q ≈ r → E ⊢ Γ ▹ p ≈ r

\end{code}



#### Soundness of the inference rules

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)


\begin{code}

module Soundness {χ α ρ ι : Level}{I : Type ι} (E : I → Eq{χ})
                 (M : SetoidAlgebra α ρ)     -- We assume an algebra M
                 (V : M ⊧ E)         -- that models all equations in E.
                 where
 open SetoidAlgebra M

 -- In any model M that satisfies the equations E, derived equality is actual equality.
 open SetoidReasoning Domain

 open Environment M
 sound : ∀ {p q} → E ⊢ Γ ▹ p ≈ q → M ⊨ (p ≐ q)

 sound (hyp i)                      =  V i
 sound (app {f = f} es) ρ           =  Interp .cong (≡-refl , λ i → sound (es i) ρ)
 sound (sub {p = p} {q} Epq σ) ρ    =  begin
                                       ⦅ p [ σ ] ⦆ .apply ρ          ≈⟨ substitution p σ ρ ⟩
                                       ⦅ p       ⦆ .apply (⦅ σ ⦆s ρ) ≈⟨ sound Epq (⦅ σ ⦆s ρ)  ⟩
                                       ⦅ q       ⦆ .apply (⦅ σ ⦆s ρ) ≈˘⟨ substitution  q σ ρ ⟩
                                       ⦅ q [ σ ] ⦆ .apply ρ          ∎

 sound (refl {p = p})               = isEquiv .reflE {x = p}
 sound (sym {p = p} {q} Epq)        = isEquiv .symmE {x = p} {q} (sound Epq)
 sound (trans{p = p}{q}{r} Epq Eqr) = isEquiv .tranE {i = p}{q}{r}(sound Epq)(sound Eqr)


\end{code}

The deductive closure of a set E is the set of equations modeled by all models of E; that is, Th Mod E.

The soundness proof above shows ∀ X → E ⊢ X ▹ p ≈ q → (p , q) ∈ Th Mod ℰ.
That is,  ∀ X → E ⊢ X ▹ p ≈ q → Mod E ⊫ p ≈ q.

The converse is Birkhoff's completeness theorem: if Mod E ⊫ p ≈ q, then E ⊢ X ▹ p ≈ q.

We will prove that result next.

#### Birkhoff's completeness theorem

The proof proceeds by constructing a relatively free algebra consisting of term
quotiented by derivable equality E ⊢ Γ ▹ _≈_.  It then suffices to prove
that this model satisfies all equations in $E$.

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)

\begin{code}

-- Universal model
-- A term model for E and Γ is Term Γ modulo E ⊢ Γ ▹ _≈_.
module TermModel {χ ι : Level}{Γ : Type χ}{I : Type ι} (E : I → Eq) where
 open SetoidAlgebra

 -- Term Γ s quotiented by E⊢Γ▹·≡·.
 TermSetoid : Type χ → Setoid _ _
 TermSetoid Γ .Carrier               = Term Γ
 TermSetoid Γ ._≈_                   = E ⊢ Γ ▹_≈_
 TermSetoid Γ .isEquivalence .reflE  = refl
 TermSetoid Γ .isEquivalence .symmE   = sym
 TermSetoid Γ .isEquivalence .tranE = trans

 -- The interpretation of an operation is simply the operation itself.
 -- This works since E ⊢ Γ ▹_≈_ is a congruence.
 TermInterp : ∀ {Γ} → Func (⟦ 𝑆 ⟧s (TermSetoid Γ)) (TermSetoid Γ)
 apply TermInterp (f , ts) = node f ts
 cong TermInterp (≡-refl , h) = app h

 -- The term model per context Γ.
 M : Type χ → SetoidAlgebra _ _
 Domain (M Γ) = TermSetoid Γ
 Interp (M Γ) = TermInterp

 open Environment (M Γ)

 -- The identity substitution σ₀ maps variables to themselves.
 σ₀ : {Γ : Type χ} → Sub Γ Γ
 σ₀ x = ℊ x

 -- σ₀ acts indeed as identity.
 identity : (t : Term Γ) → E ⊢ Γ ▹ t [ σ₀ ] ≈ t
 identity (ℊ x) = refl
 identity (node f ts) = app λ i → identity (ts i)

 -- Evaluation in the term model is substitution $E ⊢ Γ ▹ ⦅t⦆σ ≡ t[σ]$.
 -- This would even hold "up to the nose" if we had function extensionality.

 evaluation : (t : Term Δ) (σ : Sub Γ Δ) → E ⊢ Γ ▹ (apply ⦅ t ⦆ σ) ≈ (t [ σ ])
 evaluation (ℊ x)    σ = refl
 evaluation (node f ts)  σ = app (λ i → evaluation (ts i) σ)

 -- The term model satisfies all the equations it started out with.
 satisfies : ∀ i → M Γ ⊨ E i
 satisfies i σ = begin
                 apply ⦅ p ⦆ σ  ≈⟨ evaluation p σ ⟩
                 p [ σ ]        ≈⟨ sub (hyp i) σ ⟩
                 q [ σ ]        ≈˘⟨ evaluation q σ ⟩
                 apply ⦅ q ⦆ σ  ∎
                 where
                  open SetoidReasoning (TermSetoid _)
                  p = lhs (E i)
                  q = rhs (E i)

\end{code}

#### Birkhoff's Completeness Theorem

(Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem;
see: http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf)


\begin{code}

module Completeness {χ ι : Level}{I : Type ι} (E : I → Eq{χ}) {Γ} where
 open TermModel {Γ = Γ} E
 open Environment (M Γ)

 -- Birkhoff's completeness theorem [Birkhoff (1935)]:
 -- Any valid consequence is derivable.
 completeness : ∀ p q → Mod E ⊫ (p ≐ q) → E ⊢ Γ ▹ p ≈ q
 completeness p q V = begin
                  p              ≈˘⟨ identity p ⟩
                  p [ σ₀ ]       ≈˘⟨ evaluation p σ₀ ⟩
                  apply ⦅ p ⦆ σ₀  ≈⟨ V (M Γ) satisfies σ₀ ⟩
                  apply ⦅ q ⦆ σ₀  ≈⟨ evaluation q σ₀ ⟩
                  q [ σ₀ ]       ≈⟨ identity q ⟩
                  q              ∎
                  where open SetoidReasoning (TermSetoid Γ)


\end{code}






--------------------------------------

[the agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team






-- ℰ ⊢ p ≈ q is valid iff p ≈ q holds in all models that satify all equations in ℰ.
-- _⊢_≈_ : Pred(Term X × Term X) (ov α) → Term X → Term X → Type (ov (χ ⊔ α))
-- ℰ ⊢ p ≈ q = Mod ℰ ⊫ p ≈ q


