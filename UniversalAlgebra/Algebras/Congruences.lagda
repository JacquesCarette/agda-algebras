---
layout: default
title : Algebras.Congruences module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="congruence-relations">Congruence Relations</a>
This section presents the [Algebras.Congruences][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Level renaming ( suc to lsuc )
open import Algebras.Basic

module Algebras.Congruences {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where

open import Axiom.Extensionality.Propositional    renaming (Extensionality to funext)
open import Agda.Builtin.Equality                 using    ( _≡_      ; refl    )
open import Agda.Primitive                        using    ( _⊔_                )
                                                  renaming ( Set      to  Type  )

open import Relation.Binary                       using    ( IsEquivalence      )
                                                  renaming ( Rel      to BinRel )

open import Data.Product                          using    ( _,_      ;   Σ
                                                           ; Σ-syntax ;   _×_   )
open import Relation.Binary.PropositionalEquality using    ( sym ; trans ; cong )

open import Algebras.Products      𝑆  using (ov)
open import Overture.Preliminaries    using (∣_∣; ∥_∥)
open import Relations.Discrete        using (0[_] ; _|:_)
open import Relations.Quotients       using (_/_; ⟪_⟫; IsBlock)

private variable α β ρ : Level
\end{code}

A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of `𝑨`.  This concept can be represented in a number of alternative but equivalent ways.
Formally, we define a record type (`IsCongruence`) to represent the property of being a congruence, and we define a Sigma type (`Con`) to represent the type of congruences of a given algebra.

\begin{code}

record IsCongruence (𝑨 : Algebra α 𝑆)(θ : BinRel ∣ 𝑨 ∣ ρ) : Type(ov ρ ⊔ α)  where
 constructor mkcon
 field       is-equivalence : IsEquivalence θ
             is-compatible  : compatible 𝑨 θ

Con : (𝑨 : Algebra α 𝑆) → Type(α ⊔ ov ρ)
Con {α}{ρ}𝑨 = Σ[ θ ∈ ( BinRel ∣ 𝑨 ∣ ρ ) ] IsCongruence 𝑨 θ

\end{code}

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

\begin{code}

IsCongruence→Con : {𝑨 : Algebra α 𝑆}(θ : BinRel ∣ 𝑨 ∣ ρ) → IsCongruence 𝑨 θ → Con 𝑨
IsCongruence→Con θ p = θ , p

Con→IsCongruence : {𝑨 : Algebra α 𝑆} → ((θ , _) : Con{α}{ρ} 𝑨) → IsCongruence 𝑨 θ
Con→IsCongruence θ = ∥ θ ∥

\end{code}

#### <a id="example">Example</a>
We defined the *zero relation* `𝟎` in the [Relations.Discrete][] module.  We now build the *trivial congruence*, which has `𝟎` as its underlying relation. Observe that `𝟎` is equivalent to the identity relation `≡` and these are obviously both equivalence relations. In fact, we already proved this of `≡` in the [Overture.Equality][] module, so we simply apply the corresponding proofs.

\begin{code}

𝟎-IsEquivalence : {A : Type α} →  IsEquivalence {A = A} 0[ A ]
𝟎-IsEquivalence = record { refl = refl ; sym = sym; trans = trans }

\end{code}

Next we formally record another obvious fact---that `𝟎-rel` is compatible with all operations of all algebras.

\begin{code}

𝟎-compatible-op : funext 𝓥 α → {𝑨 : Algebra α 𝑆} (𝑓 : ∣ 𝑆 ∣) → (𝑓 ̂ 𝑨) |: 0[ ∣ 𝑨 ∣ ]
𝟎-compatible-op fe {𝑨} 𝑓 {i}{j} ptws0  = cong (𝑓 ̂ 𝑨) (fe ptws0)

𝟎-compatible : funext 𝓥 α → {𝑨 : Algebra α 𝑆} → compatible 𝑨 0[ ∣ 𝑨 ∣ ]
𝟎-compatible fe {𝑨} = λ 𝑓 x → 𝟎-compatible-op fe {𝑨} 𝑓 x

\end{code}

Finally, we have the ingredients need to construct the zero congruence of any algebra we like.

\begin{code}

Δ : (𝑨 : Algebra α 𝑆){fe : funext 𝓥 α} → IsCongruence 𝑨 0[ ∣ 𝑨 ∣ ]
Δ 𝑨 {fe} = mkcon 𝟎-IsEquivalence (𝟎-compatible fe)

𝟘 : (𝑨 : Algebra α 𝑆){fe : funext 𝓥 α} → Con{α} 𝑨
𝟘 𝑨 {fe} = IsCongruence→Con 0[ ∣ 𝑨 ∣ ] (Δ 𝑨 {fe})

\end{code}


A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

#### <a id="quotient-algebras">Quotient algebras</a>
In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.<sup>[1](Algebras.Congruences.html#fn1)</sup>

\begin{code}

_╱_ : (𝑨 : Algebra α 𝑆) → Con{α}{ρ} 𝑨 → Algebra (α ⊔ lsuc ρ) 𝑆

𝑨 ╱ θ = (∣ 𝑨 ∣ / ∣ θ ∣)  ,                                  -- the domain of the quotient algebra
        λ 𝑓 𝑎 → ⟪ (𝑓 ̂ 𝑨)(λ i →  IsBlock.block-u ∥ 𝑎 i ∥) ⟫  -- the basic operations of the quotient algebra

\end{code}

**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.

\begin{code}


𝟘[_╱_] : (𝑨 : Algebra α 𝑆)(θ : Con{α}{ρ} 𝑨) → BinRel (∣ 𝑨 ∣ / ∣ θ ∣)(α ⊔ lsuc ρ)
𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.

\begin{code}

𝟎[_╱_] : (𝑨 : Algebra α 𝑆)(θ : Con{α}{ρ} 𝑨){fe : funext 𝓥 (α ⊔ lsuc ρ)} → Con (𝑨 ╱ θ)
𝟎[ 𝑨 ╱ θ ] {fe} = 𝟘[ 𝑨 ╱ θ ] , Δ (𝑨 ╱ θ) {fe}

\end{code}


Finally, the following elimination rule is sometimes useful (but it 'cheats' a lot by baking in
a large amount of extensionality that is miraculously true).

\begin{code}

open IsCongruence

/-≡ : {𝑨 : Algebra α 𝑆}(θ : Con{α}{ρ} 𝑨){u v : ∣ 𝑨 ∣} → ⟪ u ⟫ {∣ θ ∣} ≡ ⟪ v ⟫ → ∣ θ ∣ u v
/-≡ θ refl = IsEquivalence.refl (is-equivalence ∥ θ ∥)

\end{code}

--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> **Unicode Hints**. Produce the `╱` symbol in [agda2-mode][] by typing `\---` and then `C-f` a number of times.</span>


<br>
<br>

[← Algebras.Products](Algebras.Products.html)
<span style="float:right;">[Homomorphisms →](Homomorphisms.html)</span>

{% include UALib.Links.md %}
