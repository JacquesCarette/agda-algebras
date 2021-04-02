---
layout: default
title : Homomorphisms.Noether module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="homomorphism-theorems">Homomorphism Theorems</a>

This chapter presents the [Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Homomorphisms.Basic{𝑆 = 𝑆}{gfe} public

\end{code}


#### <a id="the-first-homomorphism-theorem">The First Homomorphism Theorem</a>

Here we formalize a version of the *first homomorphism theorem*, sometimes called *Noether's first homomorphism theorem*, after Emmy Noether who was among the first proponents of the abstract approach to the subject that we now call "modern algebra").

Informally, the theorem states that every homomorphism from `𝑨` to `𝑩` (`𝑆`-algebras) factors through the quotient algebra `𝑨 ╱ ker h` (`𝑨` modulo the kernel of the given homomorphism).  In other terms, given `h : hom 𝑨 𝑩` there exists `φ : hom (𝑨 ╱ ker h) 𝑩` which, when composed with the canonical projection `πker : 𝑨 ↠ 𝑨 ╱ ker h`, is equal to `h`; that is, `h = φ ∘ πker`.  Moreover, `φ` is a *monomorphism* (injective homomorphism) and is unique.

Our formal proof of this theorem will require function extensionality as well as a couple of truncation assumptions. The function extensionality postulate (`fe`) will be clear enough.  As for the truncation assumptions, we require the following:<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

+ *uniqueness of kernel-membership/kernel-block-identity proofs*: proving that `φ` is monic requires that the kernel of `h` inhabits the type `Pred₂` of *binary propositions* (postulate `ssR`) and that we are able to decide when two blocks of the kernel are equal (postulate `ssA`);

+ *uniqueness of codomain-identity proofs*: proving that `φ` is an embedding requires that the codomain `∣ 𝑩 ∣` is a *set*, that is, has unique identity proofs (postulate `Bset`).

Note that the classical, informal statement of the theorem does not demand that `φ` be an embedding (in our sense of having subsingleton fibers), and if we left this out of the consequent of the formal theorem statement below, then we could omit from the antecedent the assumption that ∣ 𝑩 ∣ is a set.

Without further ado, we present our formalization of the first homomorphism theorem.<sup>[2](Homomorphisms.Noether.html#fn2)</sup>

\begin{code}

open Congruence

module _ {𝓤 𝓦 : Universe}
         -- extensionality assumptions --
            (fe : dfunext 𝓥 𝓦)
            (pe : prop-ext 𝓤 𝓦)

         (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)

         -- truncation assumptions --
            (Bset : is-set ∣ 𝑩 ∣)
            (ssR : ∀ a x → is-subsingleton (⟨ kercon 𝑩 h ⟩ a x))
            (ssA : ∀ C → is-subsingleton (𝒞 ⟨ kercon 𝑩 h ⟩ C))
 where

 FirstHomomorphismTheorem :

  Σ φ ꞉ hom (𝑨 [ 𝑩 ]/ker h) 𝑩 ,
       (∣ h ∣ ≡ ∣ φ ∣ ∘ ∣ πker 𝑩 h ∣) × Monic ∣ φ ∣ × is-embedding ∣ φ ∣

 FirstHomomorphismTheorem = (φ , φhom) , φcom , φmon , φemb
  where
  θ : Congruence 𝑨
  θ = kercon 𝑩 h

  φ : ∣ 𝑨 [ 𝑩 ]/ker h ∣ → ∣ 𝑩 ∣
  φ a = ∣ h ∣ ⌜ a ⌝

  𝑹 : Pred₂ ∣ 𝑨 ∣ 𝓦
  𝑹 = ⟨ kercon 𝑩 h ⟩ , ssR

  φhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h) 𝑩 φ
  φhom 𝑓 𝒂 =  ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌜ 𝒂 x ⌝) ) ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌜ 𝒂 x ⌝)  ⟩
             (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌜ 𝒂 x ⌝)) ≡⟨ ap (𝑓 ̂ 𝑩) (fe λ x → refl) ⟩
             (𝑓 ̂ 𝑩) (λ x → φ (𝒂 x))             ∎

  φmon : Monic φ
  φmon (.(⟨ θ ⟩ u) , u , refl) (.(⟨ θ ⟩ v) , v , refl) φuv =
   class-extensionality' {𝑹 = 𝑹} pe ssA (IsEquiv θ) φuv

  φcom : ∣ h ∣ ≡ φ ∘ ∣ πker 𝑩 h ∣
  φcom = refl

  φemb : is-embedding φ
  φemb = monic-is-embedding|sets φ Bset φmon

\end{code}

Next we prove that the homomorphism `φ`, whose existence we just proved, is unique.

\begin{code}

 NoetherHomUnique : (f g : hom (𝑨 [ 𝑩 ]/ker h) 𝑩)
  →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣
  →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩 h ∣
                    ---------------------------------
  →                 ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherHomUnique f g hfk hgk (.(⟨ kercon 𝑩 h ⟩ a) , a , refl) =

  let θ = (⟨ kercon 𝑩 h ⟩ a , a , refl) in

   ∣ f ∣ θ   ≡⟨ cong-app(hfk ⁻¹)a ⟩  ∣ h ∣ a   ≡⟨ cong-app(hgk)a ⟩   ∣ g ∣ θ   ∎

\end{code}

If we postulate function extensionality, then we obtain the following variation of the last result.<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

 fe-NoetherHomUnique : funext (𝓤 ⊔ 𝓦 ⁺) 𝓦 → (f g : hom (𝑨 [ 𝑩 ]/ker h) 𝑩)
  →                    ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣ → ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩 h ∣ → ∣ f ∣ ≡ ∣ g ∣
 fe-NoetherHomUnique fe f g hfk hgk = fe (NoetherHomUnique f g hfk hgk)

\end{code}

If we assume the hypotheses of the first homomorphism theorem and add the assumption that `h` is epic, then we get the so-called *first isomorphism theorem*.

\begin{code}

 FirstIsomorphismTheorem : dfunext 𝓦 𝓦 → Epic ∣ h ∣

  →    Σ f ꞉ (epi (𝑨 [ 𝑩 ]/ker h) 𝑩) , (∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣) × is-embedding ∣ f ∣

 FirstIsomorphismTheorem fev hE = (fmap , fhom , fepic) , refl , femb
  where
  θ : Congruence 𝑨
  θ = kercon 𝑩 h

  fmap : ∣ 𝑨 [ 𝑩 ]/ker h ∣ → ∣ 𝑩 ∣
  fmap ⟪a⟫ = ∣ h ∣ ⌜ ⟪a⟫ ⌝

  fhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h) 𝑩 fmap
  fhom 𝑓 𝒂 =  ∣ h ∣((𝑓 ̂ 𝑨) λ x → ⌜ 𝒂 x ⌝)   ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌜ 𝒂 x ⌝)  ⟩
              (𝑓 ̂ 𝑩)(∣ h ∣ ∘ λ x → ⌜ 𝒂 x ⌝) ≡⟨ ap(𝑓 ̂ 𝑩)(fe λ _ → refl)⟩
              (𝑓 ̂ 𝑩) (fmap ∘ 𝒂)              ∎

  fepic : Epic fmap
  fepic b = γ where
   a : ∣ 𝑨 ∣
   a = EpicInv ∣ h ∣ hE b

   bfa : b ≡ fmap ⟪ a ⟫
   bfa = (cong-app (EpicInvIsRightInv {fe = fev} ∣ h ∣ hE) b)⁻¹

   γ : Image fmap ∋ b
   γ = Image_∋_.eq b ⟪ a ⟫ bfa

  fmon : Monic fmap
  fmon (.(⟨ θ ⟩ u) , u , refl) (.(⟨ θ ⟩ v) , v , refl) fuv =
   class-extensionality' {𝑹 = ⟨ kercon 𝑩 h ⟩ , ssR} pe ssA (IsEquiv θ) fuv

  femb : is-embedding fmap
  femb = monic-is-embedding|sets fmap Bset fmon

\end{code}

The argument used above to prove `NoetherHomUnique` can also be used to prove uniqueness of the epimorphism `f` found in the isomorphism theorem.

\begin{code}

 NoetherIsoUnique : (f g : epi (𝑨 [ 𝑩 ]/ker h) 𝑩) → ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 h ∣
  →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩 h ∣ → ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherIsoUnique f g hfk hgk (.(⟨ kercon 𝑩 h ⟩ a) , a , refl) =

  let θ = (⟨ kercon 𝑩 h ⟩ a , a , refl) in

   ∣ f ∣ θ  ≡⟨ cong-app (hfk ⁻¹) a ⟩  ∣ h ∣ a  ≡⟨ cong-app (hgk) a ⟩  ∣ g ∣ θ  ∎

\end{code}





#### <a id="homomorphism-composition">Homomorphism composition</a>

The composition of homomorphisms is again a homomorphism.  We formalize this in a number of alternative ways.

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 ∘-hom : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
  →       hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪

 ∘-hom 𝑨 {𝑩} 𝑪 (g , ghom) (h , hhom) = h ∘ g , γ where

  γ : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)

  γ 𝑓 a = (h ∘ g) ((𝑓 ̂ 𝑨) a) ≡⟨ ap h ( ghom 𝑓 a ) ⟩
          h ((𝑓 ̂ 𝑩) (g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
          (𝑓 ̂ 𝑪) (h ∘ g ∘ a) ∎


 ∘-is-hom : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
            {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
  →         is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g
  →         is-homomorphism 𝑨 𝑪 (g ∘ f)

 ∘-is-hom 𝑨 𝑪 {f} {g} fhom ghom = ∥ ∘-hom 𝑨 𝑪 (f , fhom) (g , ghom) ∥

\end{code}



#### <a id="homomorphism-decomposition">Homomorphism decomposition</a>

If `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is surjective, and `ker h ⊆ ker g`, then there exists `φ : hom 𝑪 𝑩` such that `g = φ ∘ h`, that is, such that the following diagram commutes;

```
𝑨---- h -->>𝑪
 \         .
  \       .
   g     ∃φ
    \   .
     \ .
      V
      𝑩
```

This, or some variation of it, is sometimes referred to as the Second Isomorphism Theorem.  We formalize its statement and proof as follows. (Notice that the proof is constructive.)

\begin{code}

homFactor : {𝓤 : Universe} → funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          kernel ∣ h ∣ ⊆ kernel ∣ g ∣  →   Epic ∣ h ∣
            -------------------------------------------
 →          Σ φ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ φ ∣ ∘ ∣ h ∣

homFactor fe{𝑨}{𝑩}{𝑪}(g , ghom)(h , hhom) Kh⊆Kg hEpi = (φ , φIsHomCB) , gφh
 where
 hInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
 hInv = λ c → (EpicInv h hEpi) c

 φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
 φ = λ c → g ( hInv c )

 ξ : ∀ x → kernel h (x , hInv (h x))
 ξ x = (cong-app (EpicInvIsRightInv {fe = fe} h hEpi) (h x))⁻¹

 gφh : g ≡ φ ∘ h
 gφh = fe  λ x → Kh⊆Kg (ξ x)

 ζ : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣)(x : ∥ 𝑆 ∥ 𝑓) →  𝒄 x ≡ (h ∘ hInv)(𝒄 x)
 ζ  𝑓 𝒄 x = (cong-app (EpicInvIsRightInv {fe = fe} h hEpi) (𝒄 x))⁻¹

 ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) →  𝒄 ≡ h ∘ (hInv ∘ 𝒄)
 ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄)(EpicInvIsRightInv {fe = fe} h hEpi)⁻¹

 useker : ∀ 𝑓 𝒄 → g(hInv (h((𝑓 ̂ 𝑨)(hInv ∘ 𝒄)))) ≡ g((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))
 useker 𝑓 c = Kh⊆Kg (cong-app (EpicInvIsRightInv{fe = fe} h hEpi)
                              (h ((𝑓 ̂ 𝑨)(hInv ∘ c))) )

 φIsHomCB : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) → φ((𝑓 ̂ 𝑪) 𝒄) ≡ (𝑓 ̂ 𝑩)(φ ∘ 𝒄)

 φIsHomCB 𝑓 𝒄 =  g (hInv ((𝑓 ̂ 𝑪) 𝒄))              ≡⟨ i   ⟩
                g (hInv ((𝑓 ̂ 𝑪)(h ∘ (hInv ∘ 𝒄)))) ≡⟨ ii  ⟩
                g (hInv (h ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))))   ≡⟨ iii ⟩
                g ((𝑓 ̂ 𝑨)(hInv ∘ 𝒄))              ≡⟨ iv  ⟩
                (𝑓 ̂ 𝑩)(λ x → g (hInv (𝒄 x)))      ∎
  where
  i   = ap (g ∘ hInv) (ap (𝑓 ̂ 𝑪) (ι 𝑓 𝒄))
  ii  = ap (g ∘ hInv) (hhom 𝑓 (hInv ∘ 𝒄))⁻¹
  iii = useker 𝑓 𝒄
  iv  = ghom 𝑓 (hInv ∘ 𝒄)

\end{code}

Here's a more general version.

```
𝑨 --- γ ->> 𝑪
 \         .
  \       .
   β     ∃φ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

module _ {𝓧 𝓨 𝓩 : Universe} where

 HomFactor : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
             (β : hom 𝑨 𝑩) (γ : hom 𝑨 𝑪)
  →          Epic ∣ γ ∣ → (kernel ∣ γ ∣) ⊆ (kernel ∣ β ∣)
             --------------------------------------------
  →          Σ φ ꞉ (hom 𝑪 𝑩) , ∣ β ∣ ≡ ∣ φ ∣ ∘ ∣ γ ∣

 HomFactor 𝑨 {𝑩}{𝑪} β γ γE Kγβ = (φ , φIsHomCB) , βφγ
  where
  γInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  γInv = λ y → (EpicInv ∣ γ ∣ γE) y

  φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  φ = λ y → ∣ β ∣ ( γInv y )

  ξ : (x : ∣ 𝑨 ∣) → kernel ∣ γ ∣ (x , γInv (∣ γ ∣ x))
  ξ x =  ( cong-app (EpicInvIsRightInv{fe = gfe} ∣ γ ∣ γE) ( ∣ γ ∣ x ) )⁻¹

  βφγ : ∣ β ∣ ≡ φ ∘ ∣ γ ∣
  βφγ = gfe λ x → Kγβ (ξ x)

  ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) → 𝒄 ≡  ∣ γ ∣ ∘ (γInv ∘ 𝒄)
  ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄) (EpicInvIsRightInv{fe = gfe} ∣ γ ∣ γE)⁻¹

  useker : ∀ 𝑓 𝒄 → ∣ β ∣ (γInv (∣ γ ∣ ((𝑓 ̂ 𝑨) (γInv ∘ 𝒄)))) ≡ ∣ β ∣((𝑓 ̂ 𝑨) (γInv ∘ 𝒄))
  useker 𝑓 𝒄 = Kγβ (cong-app (EpicInvIsRightInv {fe = gfe} ∣ γ ∣ γE)
                             (∣ γ ∣ ((𝑓 ̂ 𝑨)(γInv ∘ 𝒄))))

  φIsHomCB : ∀ 𝑓 𝒄 → φ ((𝑓 ̂ 𝑪) 𝒄) ≡ ((𝑓 ̂ 𝑩)(φ ∘ 𝒄))

  φIsHomCB 𝑓 𝒄 = ∣ β ∣ (γInv ((𝑓 ̂ 𝑪) 𝒄))                   ≡⟨ i   ⟩
                ∣ β ∣ (γInv ((𝑓 ̂ 𝑪)(∣ γ ∣ ∘ (γInv ∘ 𝒄)))) ≡⟨ ii  ⟩
                ∣ β ∣ (γInv (∣ γ ∣ ((𝑓 ̂ 𝑨)(γInv ∘ 𝒄))))   ≡⟨ iii ⟩
                ∣ β ∣ ((𝑓 ̂ 𝑨)(γInv ∘ 𝒄))                  ≡⟨ iv  ⟩
                ((𝑓 ̂ 𝑩)(λ x → ∣ β ∣ (γInv (𝒄 x))))        ∎
   where
   i   = ap (∣ β ∣ ∘ γInv) (ap (𝑓 ̂ 𝑪) (ι 𝑓 𝒄))
   ii  = ap (∣ β ∣ ∘ γInv) (∥ γ ∥ 𝑓 (γInv ∘ 𝒄))⁻¹
   iii = useker 𝑓 𝒄
   iv  = ∥ β ∥ 𝑓 (γInv ∘ 𝒄)

\end{code}

If, in addition, both β and γ are epic, then so is φ.

\begin{code}

 HomFactorEpi : (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
                (β : hom 𝑨 𝑩) (βe : Epic ∣ β ∣)
                (ξ : hom 𝑨 𝑪) (ξe : Epic ∣ ξ ∣)
  →             (kernel ∣ ξ ∣) ⊆ (kernel ∣ β ∣)
                ----------------------------------
  →             Σ φ ꞉ (epi 𝑪 𝑩) , ∣ β ∣ ≡ ∣ φ ∣ ∘ ∣ ξ ∣

 HomFactorEpi 𝑨 {𝑩}{𝑪} β βe ξ ξe kerincl = (fst ∣ φF ∣ , (snd ∣ φF ∣ , φE)) , ∥ φF ∥
  where
  φF : Σ φ ꞉ (hom 𝑪 𝑩) , ∣ β ∣ ≡ ∣ φ ∣ ∘ ∣ ξ ∣
  φF = HomFactor  𝑨 {𝑩}{𝑪} β ξ ξe kerincl

  ξinv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  ξinv = λ c → (EpicInv ∣ ξ ∣ ξe) c

  βinv : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  βinv = λ b → (EpicInv ∣ β ∣ βe) b

  φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  φ = λ c → ∣ β ∣ ( ξinv c )

  φE : Epic φ
  φE = epic-factor {fe = gfe} ∣ β ∣ ∣ ξ ∣ φ ∥ φF ∥ βe

\end{code}


--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> See [Relations.Truncation][] for a discussion of *truncation*, *sets*, and *uniqueness of proofs*.</span>

<sup>2</sup><span class="footnote" id="fn2"> In this module we are already assuming *global* function extensionality (`gfe`), and we could just appeal to `gfe` (e.g., in the proof of `FirstHomomorphismTheorem`) instead of adding local function extensionality (\ab{fe}) to the list of assumptions.  However, we sometimes add an extra extensionality postulate in order to highlight where and how the principle is applied.}</span>

<br>
<br>

[← Homomorphisms.Basic](Homomorphisms.Basic.html)
<span style="float:right;">[Homomorphisms.Isomorphisms →](Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
