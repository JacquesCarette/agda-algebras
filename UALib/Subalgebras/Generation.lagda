---
layout: default
title : UALib.Subalgebras.Generation module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="subuniverse-generation">Subuniverse generation</a>

This section presents the [UALib.Subalgebras.Generation][] module of the [Agda Universal Algebra Library][].

Here we define the inductive type of the subuniverse generated by a given collection of elements from the domain of an algebra, and prove that what we have defined is indeed the smallest subuniverse containing the given elements.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Subalgebras.Generation
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Subalgebras.Subuniverses{𝑆 = 𝑆}{gfe}{𝕏} public


data Sg {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆) (X : Pred ∣ 𝑨 ∣ 𝓦) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤) where
 var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
 app : (f : ∣ 𝑆 ∣){a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣} → Im a ⊆ Sg 𝑨 X
       ---------------------------------------------
  →       (f ̂ 𝑨) a ∈ Sg 𝑨 X

sgIsSub : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆}{X : Pred ∣ 𝑨 ∣ 𝓦} → Sg 𝑨 X ∈ Subuniverses 𝑨
sgIsSub f a α = app f α

sgIsSmallest : {𝓤 𝓦 𝓡 : Universe}(𝑨 : Algebra 𝓤 𝑆){X : Pred ∣ 𝑨 ∣ 𝓦}(Y : Pred ∣ 𝑨 ∣ 𝓡)
 →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y
              ------------------------------
 →                     Sg 𝑨 X ⊆ Y

-- By induction on x ∈ Sg X, show x ∈ Y
sgIsSmallest _ _ _ X⊆Y (var v∈X) = X⊆Y v∈X

sgIsSmallest 𝑨 Y YIsSub X⊆Y (app f {a} ima⊆SgX) = app∈Y
 where
  -- First, show the args are in Y
  ima⊆Y : Im a ⊆ Y
  ima⊆Y i = sgIsSmallest 𝑨 Y YIsSub X⊆Y (ima⊆SgX i)

  --Since Y is a subuniverse of 𝑨, it contains the application
  app∈Y : (f ̂ 𝑨) a ∈ Y          --           of f to said args.
  app∈Y = YIsSub f a ima⊆Y
\end{code}

---------------------------------

[← UALib.Subalgebras.Subuniverses](UALib.Subalgebras.Subuniverses.html)
<span style="float:right;">[UALib.Subalgebras.Properties →](UALib.Subalgebras.Properties.html)</span>

{% include UALib.Links.md %}