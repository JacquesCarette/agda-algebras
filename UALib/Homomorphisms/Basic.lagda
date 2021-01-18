---
layout: default
title : UALib.Homomorphisms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="basic-definitions">Basic Definitions</a>

This section describes the [UALib.Homomorphisms.Basic] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)

module UALib.Homomorphisms.Basic {𝑆 : Signature 𝓞 𝓥} where

open import UALib.Relations.Congruences{𝑆 = 𝑆} public
open import UALib.Prelude.Preliminaries using (_≡⟨_⟩_; _∎) public

\end{code}

The definition of homomorphism in the [Agda UALib][] is an *extensional* one. What this means will become clear once we have presented the definitions.

First, we say what it means for an operation 𝑓, interpreted in the algebras 𝑨 and 𝑩, to commute with a function g : A → B.

\begin{code}

compatible-op-map : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)
                    (𝑓 : ∣ 𝑆 ∣)(g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇

compatible-op-map 𝑨 𝑩 𝑓 g = ∀ 𝒂 → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)
\end{code}

Note the appearance of the shorthand `∀ 𝒂` in the definition of `compatible-op-map`.  We can get away with this in place of `(𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣)` since Agda is able to infer that the `𝒂` here must be a tuple on ∣ 𝑨 ∣ of "length" `∥ 𝑆 ∥ 𝑓` (the arity of 𝑓).

\begin{code}

op_interpreted-in_and_commutes-with : {𝓠 𝓤 : Universe}
  (𝑓 : ∣ 𝑆 ∣) (𝑨 : Algebra 𝓠 𝑆) (𝑩 : Algebra 𝓤 𝑆)
  (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g = compatible-op-map 𝑨 𝑩 𝑓 g

\end{code}

We now define the type `hom 𝑨 𝑩` of homomorphisms from 𝑨 to 𝑩 by first defining the property `is-homomorphism` as follows.

\begin{code}

is-homomorphism : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆) → (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
is-homomorphism 𝑨 𝑩 g = ∀ (𝑓 : ∣ 𝑆 ∣) → compatible-op-map 𝑨 𝑩 𝑓 g

hom : {𝓠 𝓤 : Universe} → Algebra 𝓠 𝑆 → Algebra 𝓤 𝑆  → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ̇
hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 g

\end{code}

---------------------------------------------

#### <a id="examples">Examples</a>

A simple example is the identity map, which is proved to be a homomorphism as follows.

\begin{code}

𝒾𝒹 : {𝓤 : Universe} (A : Algebra 𝓤 𝑆) → hom A A
𝒾𝒹 _ = (λ x → x) , λ _ _ → 𝓇ℯ𝒻𝓁

id-is-hom : {𝓤 : Universe}{𝑨 : Algebra 𝓤 𝑆} → is-homomorphism 𝑨 𝑨 (𝑖𝑑 ∣ 𝑨 ∣)
id-is-hom = λ _ _ → refl _

\end{code}

We conclude this module by defining the equalizer of two functions and the equalizer of two homomorphisms.

\begin{code}

--Equalizers of functions
𝑬 : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}(g h : A → B) → Pred A 𝓦
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}(g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓦
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x

\end{code}

We will define subuniverses in the [UALib.Subalgebras.Subuniverses] module, but we note here that the equalizer of homomorphisms from 𝑨 to 𝑩 will turn out to be subuniverse of 𝑨.  Indeed, this is easily proved as follows.

\begin{code}

𝑬𝑯-is-closed : {𝓤 𝓦 : Universe} → funext 𝓥 𝓦
 →              {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
                (g h : hom 𝑨 𝑩) {𝑓 : ∣ 𝑆 ∣ } (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
 →              ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
               --------------------------------------------------
 →               ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

𝑬𝑯-is-closed fe {𝑨}{𝑩} g h {𝑓} 𝒂 p =
                  (∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)) ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
                  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
                  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
                  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)   ∎

\end{code}

--------------------------------------

[↑ UALib.Homomorphisms](UALib.Homomorphisms.html)
<span style="float:right;">[UALib.Homomorphisms.Kernels →](UALib.Homomorphisms.Kernels.html)</span>

{% include UALib.Links.md %}
