---
layout: default
title : UALib.Relations.Congruences module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="congruence-relation-types">Congruence Relation Types</a>

This section presents the [UALib.Relations.Congruences][] module of the [Agda Universal Algebra Library][].

Notice that we begin the module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)

module UALib.Relations.Congruences {𝑆 : Signature 𝓞 𝓥} where

open import UALib.Relations.Quotients hiding (Signature; 𝓞; 𝓥) public

Con : {𝓤 : Universe}(A : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
Con {𝓤} A = Σ θ ꞉ ( Rel ∣ A ∣ 𝓤 ) , IsEquivalence θ × compatible A θ

con : {𝓤 : Universe}(A : Algebra 𝓤 𝑆)  →  Pred (Rel ∣ A ∣ 𝓤) (𝓞 ⊔ 𝓥 ⊔ 𝓤)
con A = λ θ → IsEquivalence θ × compatible A θ

record Congruence {𝓤 𝓦 : Universe} (A : Algebra 𝓤 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇  where
 constructor mkcon
 field
  ⟨_⟩ : Rel ∣ A ∣ 𝓦
  Compatible : compatible A ⟨_⟩
  IsEquiv : IsEquivalence ⟨_⟩

open Congruence

compatible-equivalence : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ̇
compatible-equivalence {𝓤}{𝓦} {𝑨} R = compatible 𝑨 R × IsEquivalence R

\end{code}

#### Example

We construct the *trivial* (or "diagonal" or "identity") relation and prove it is a congruence as follows.


\begin{code}

Δ : {𝓤 : Universe} → funext 𝓥 𝓤 → (A : Algebra 𝓤 𝑆) → Congruence A
Δ fe A = mkcon 𝟎-rel ( 𝟎-compatible fe ) ( 𝟎-IsEquivalence )

\end{code}

#### Quotient algebras

An important construction in universal algebra is the quotient of an algebra 𝑨 with respect to a congruence relation θ of 𝑨.  This quotient is typically denote by 𝑨 / θ and Agda allows us to define and express quotients using the standard notation.

\begin{code}

_╱_ : {𝓤 𝓡 : Universe}(A : Algebra 𝓤 𝑆) -- type ╱ with `\---` plus `C-f`
 →      Congruence{𝓤}{𝓡} A               -- a number of times, then `\_p`
       -----------------------
 →     Algebra (𝓤 ⊔ 𝓡 ⁺) 𝑆
A ╱ θ = (( ∣ A ∣ / ⟨ θ ⟩ ) , -- carrier (i.e. domain or universe))
          (λ f args         -- operations
           → ([ (f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩) ,
             ((f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
          )
        )

\end{code}

#### Examples

The zero element of a quotient can be expressed as follows.

\begin{code}

Zero╱ : {𝓤 𝓡 : Universe}{A : Algebra 𝓤 𝑆} → (θ : Congruence{𝓤}{𝓡} A) → Rel (∣ A ∣ / ⟨ θ ⟩) (𝓤 ⊔ 𝓡 ⁺)
Zero╱ θ = λ x x₁ → x ≡ x₁

\end{code}

Finally, the following elimination rule is sometimes useful.

\begin{code}

╱-refl :{𝓤 𝓡 : Universe} (A : Algebra 𝓤 𝑆){θ : Congruence{𝓤}{𝓡} A}{a a' : ∣ A ∣}
 →   ⟦ a ⟧{⟨ θ ⟩} ≡ ⟦ a' ⟧ → ⟨ θ ⟩ a a'
╱-refl A {θ} (refl _)  = IsEquivalence.rfl (IsEquiv θ) _

\end{code}

--------------------------------------

[← UALib.Relations.Quotients](UALib.Relations.Quotients.html)
<span style="float:right;">[UALib.Homomorphisms →](UALib.Homomorphisms.html)</span>

{% include UALib.Links.md %}
