---
layout: default
title : UALib.Homomorphisms.Noether module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="homomorphism-theorems">Homomorphism Theorems</a>

This chapter presents the [UALib.Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import UALib.Prelude.Preliminaries using (global-dfunext)

module UALib.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import UALib.Homomorphisms.Kernels{𝑆 = 𝑆}{gfe} hiding (global-dfunext) public

\end{code}

-------------------------------------------

#### The First Isomorphism Theorem

Here is a version of the first isomorphism theorem.

\begin{code}

open Congruence

FirstIsomorphismTheorem : {𝓤 𝓦 : Universe}
                          (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)
                          (ϕ : hom 𝑨 𝑩) (ϕE : Epic ∣ ϕ ∣ )
                           -- extensionality assumptions:
                                 {pe : propext 𝓦}
                                 (Bset : is-set ∣ 𝑩 ∣)
 →                               (∀ a x → is-subsingleton (⟨ kercon 𝑨{𝑩} ϕ ⟩ a x))
 →                               (∀ C → is-subsingleton (𝒞{A = ∣ 𝑨 ∣}{⟨ kercon 𝑨{𝑩} ϕ ⟩} C))
         --------------------------------------------------------------------------------------
 →         Σ f ꞉ (epi (𝑨 [ 𝑩 ]/ker ϕ) 𝑩) , ( ∣ ϕ ∣ ≡ ∣ f ∣ ∘ ∣ πᵏ 𝑨 {𝑩} ϕ ∣ ) × is-embedding ∣ f ∣

FirstIsomorphismTheorem {𝓤}{𝓦} 𝑨 𝑩 ϕ ϕE {pe} Bset ssR ssA =
 (fmap , fhom , fepic) , commuting , femb
  where
   θ : Congruence 𝑨
   θ = kercon 𝑨{𝑩} ϕ

   𝑨/θ : Algebra (𝓤 ⊔ 𝓦 ⁺) 𝑆
   𝑨/θ = 𝑨 [ 𝑩 ]/ker ϕ

   fmap : ∣ 𝑨/θ ∣ → ∣ 𝑩 ∣
   fmap a = ∣ ϕ ∣ ⌜ a ⌝

   fhom : is-homomorphism 𝑨/θ 𝑩 fmap
   fhom 𝑓 𝒂 =  ∣ ϕ ∣ ( fst ∥ (𝑓 ̂ 𝑨/θ) 𝒂 ∥ ) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
             ∣ ϕ ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌜ (𝒂 x) ⌝) ) ≡⟨ ∥ ϕ ∥ 𝑓 (λ x → ⌜ (𝒂 x) ⌝)  ⟩
              (𝑓 ̂ 𝑩) (∣ ϕ ∣ ∘ (λ x → ⌜ (𝒂 x) ⌝)) ≡⟨ ap (λ - → (𝑓 ̂ 𝑩) -) (gfe λ x → 𝓇ℯ𝒻𝓁) ⟩
              (𝑓 ̂ 𝑩) (λ x → fmap (𝒂 x)) ∎

   fepic : Epic fmap
   fepic b = γ
    where
     a : ∣ 𝑨 ∣
     a = EpicInv ∣ ϕ ∣ ϕE b

     a/θ : ∣ 𝑨/θ ∣
     a/θ = ⟦ a ⟧

     bfa : b ≡ fmap a/θ
     bfa = (cong-app (EpicInvIsRightInv gfe ∣ ϕ ∣ ϕE) b)⁻¹

     γ : Image fmap ∋ b
     γ = Image_∋_.eq b a/θ bfa


   commuting : ∣ ϕ ∣ ≡ fmap ∘ ∣ πᵏ 𝑨 {𝑩} ϕ ∣
   commuting = 𝓇ℯ𝒻𝓁

   fmon : Monic fmap
   fmon (.(⟨ θ ⟩ a) , a , refl _) (.(⟨ θ ⟩ a') , a' , refl _) faa' = γ
    where
     aθa' : ⟨ θ ⟩ a a'
     aθa' = faa'

     γ : (⟨ θ ⟩ a , a , 𝓇ℯ𝒻𝓁) ≡ (⟨ θ ⟩ a' , a' , 𝓇ℯ𝒻𝓁)
     γ = class-extensionality' pe gfe ssR ssA (IsEquiv θ) aθa'

   femb : is-embedding fmap
   femb = monic-into-set-is-embedding Bset fmap fmon

\end{code}

**TODO**: Proof of uniqueness of `f` is missing.

--------------------------------------------------------------

#### Homomorphism composition

The composition of homomorphisms is again a homomorphism.

\begin{code}

module _ {𝓠 𝓤 𝓦 : Universe} where

 -- composition of homomorphisms 1
 HCompClosed : (𝑨 : Algebra 𝓠 𝑆)(𝑩 : Algebra 𝓤 𝑆)(𝑪 : Algebra 𝓦 𝑆)
  →            hom 𝑨 𝑩  →  hom 𝑩 𝑪
               --------------------
  →                 hom 𝑨 𝑪

 HCompClosed (A , FA) (B , FB) (C , FC) (g , ghom) (h , hhom) = h ∘ g , γ
   where
    γ : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f  →  A) → (h ∘ g)(FA f a) ≡ FC f (h ∘ g ∘ a)

    γ f a = (h ∘ g) (FA f a)  ≡⟨ ap h ( ghom f a ) ⟩
             h (FB f (g ∘ a)) ≡⟨ hhom f ( g ∘ a ) ⟩
             FC f (h ∘ g ∘ a) ∎

 -- composition of homomorphisms 2
 HomComp : (𝑨 : Algebra 𝓠 𝑆){𝑩 : Algebra 𝓤 𝑆}(𝑪 : Algebra 𝓦 𝑆)
  →            hom 𝑨 𝑩  →  hom 𝑩 𝑪
               --------------------
  →                 hom 𝑨 𝑪
 HomComp 𝑨 {𝑩} 𝑪 f g = HCompClosed 𝑨 𝑩 𝑪 f g

 -- composition of homomorphisms 3
∘-hom : {𝓧 𝓨 𝓩 : Universe}
        (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
        {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
 →      is-homomorphism{𝓧}{𝓨} 𝑨 𝑩 f  →  is-homomorphism{𝓨}{𝓩} 𝑩 𝑪 g
       --------------------------------------------------------------------
 →          is-homomorphism{𝓧}{𝓩} 𝑨 𝑪 (g ∘ f)

∘-hom 𝑨 𝑩 𝑪 {f} {g} fhom ghom = ∥ HCompClosed 𝑨 𝑩 𝑪 (f , fhom) (g , ghom) ∥

-- composition of homomorphisms 4
∘-Hom : {𝓧 𝓨 𝓩 : Universe}
        (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
        {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
 →      is-homomorphism{𝓧}{𝓨} 𝑨 𝑩 f  →  is-homomorphism{𝓨}{𝓩} 𝑩 𝑪 g
       --------------------------------------------------------------------
 →          is-homomorphism{𝓧}{𝓩} 𝑨 𝑪 (g ∘ f)

∘-Hom 𝑨 {𝑩} 𝑪 {f} {g} = ∘-hom 𝑨 𝑩 𝑪 {f} {g}


trans-hom : {𝓧 𝓨 𝓩 : Universe}
        (𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
        (f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣ )(g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣ )
 →      is-homomorphism{𝓧}{𝓨} 𝑨 𝑩 f  →  is-homomorphism{𝓨}{𝓩} 𝑩 𝑪 g
       --------------------------------------------------------------------
 →          is-homomorphism{𝓧}{𝓩} 𝑨 𝑪 (g ∘ f)
trans-hom {𝓧}{𝓨}{𝓩} 𝑨 𝑩 𝑪 f g = ∘-hom {𝓧}{𝓨}{𝓩} 𝑨 𝑩 𝑪 {f}{g}

\end{code}

----------------------------------------------------------

#### Homomorphism decomposition

If `g : hom 𝑨 𝑩`, `h : hom 𝑨 𝑪`, `h` is surjective, and `ker h ⊆ ker g`, then there exists `ϕ : hom 𝑪 𝑩` such that `g = ϕ ∘ h`, that is, such that the following diagram commutes;

```
𝑨---- h -->>𝑪
 \         .
  \       .
   g     ∃ϕ
    \   .
     \ .
      V
      𝑩
```

This, or some variation of it, is sometimes referred to as the Second Isomorphism Theorem.  We formalize its statement and proof as follows. (Notice that the proof is constructive.)

\begin{code}
homFactor : {𝓤 : Universe} → funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 𝑆}
            (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
 →          ker-pred ∣ h ∣ ⊆ ker-pred ∣ g ∣  →   Epic ∣ h ∣
           ---------------------------------------------
 →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

homFactor fe {𝑨 = A , FA}{𝑩 = B , FB}{𝑪 = C , FC}
 (g , ghom) (h , hhom) Kh⊆Kg hEpi = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : C → A
   hInv = λ c → (EpicInv h hEpi) c

   ϕ : C → B
   ϕ = λ c → g ( hInv c )

   ξ : (x : A) → ker-pred h (x , hInv (h x))
   ξ x =  ( cong-app (EpicInvIsRightInv fe h hEpi) ( h x ) )⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = fe  λ x → Kh⊆Kg (ξ x)

   ζ : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)(x : ∥ 𝑆 ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EpicInvIsRightInv fe h hEpi) (c x))⁻¹

   ι : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EpicInvIsRightInv fe h hEpi)⁻¹

   useker : (f : ∣ 𝑆 ∣)  (c : ∥ 𝑆 ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EpicInvIsRightInv fe h hEpi)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → C)
    →         ϕ (FC f a)  ≡  FB f (ϕ ∘ a)

   ϕIsHomCB f c =
    g (hInv (FC f c))                ≡⟨ i   ⟩
    g (hInv (FC f (h ∘ (hInv ∘ c)))) ≡⟨ ii  ⟩
    g (hInv (h (FA f (hInv ∘ c))))   ≡⟨ iii ⟩
    g (FA f (hInv ∘ c))              ≡⟨ iv  ⟩
    FB f (λ x → g (hInv (c x)))      ∎
    where
     i   = ap (g ∘ hInv) (ap (FC f) (ι f c))
     ii  = ap (λ - → g (hInv -)) (hhom f (hInv ∘ c))⁻¹
     iii = useker f c
     iv  = ghom f (hInv ∘ c)
\end{code}


--------------------------------------

[← UALib.Homomorphisms.Kernels](UALib.Homomorphisms.Kernels.html)
<span style="float:right;">[UALib.Homomorphisms.Products →](UALib.Homomorphisms.Products.html)</span>

{% include UALib.Links.md %}

<!--
module _ {𝓠 𝓤 𝓦 : Universe}{gfe : global-dfunext} where
 HomFactor : {𝑨 : Algebra 𝓠 𝑆}{𝑩 : Algebra 𝓤 𝑆}{𝑪 : Algebra 𝓦 𝑆}
             (g : hom 𝑨 𝑩) (h : hom 𝑨 𝑪)
  →          (KER-pred ∣ h ∣) ⊆ (KER-pred ∣ g ∣)  →  Epic ∣ h ∣
            ------------------------------------------------
  →           Σ ϕ ꞉ (hom 𝑪 𝑩) , ∣ g ∣ ≡ ∣ ϕ ∣ ∘ ∣ h ∣

 HomFactor {A , FA}{B , FB}{C , FC}(g , ghom)(h , hhom) Kh⊆Kg hEpi = (ϕ , ϕIsHomCB) , g≡ϕ∘h
  where
   hInv : C → A
   hInv = λ c → (EpicInv h hEpi) c

   ϕ : C → B
   ϕ = λ c → g ( hInv c )

   ξ : (x : A) → KER-pred h (x , hInv (h x))
   ξ x =  ( cong-app (EpicInvIsRightInv gfe h hEpi) ( h x ) )⁻¹

   g≡ϕ∘h : g ≡ ϕ ∘ h
   g≡ϕ∘h = gfe  λ x → Kh⊆Kg (ξ x)

   ζ : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)(x : ∥ 𝑆 ∥ f)
    →  c x ≡ (h ∘ hInv)(c x)

   ζ f c x = (cong-app (EpicInvIsRightInv gfe h hEpi) (c x))⁻¹

   ι : (f : ∣ 𝑆 ∣)(c : ∥ 𝑆 ∥ f → C)
    →  (λ x → c x) ≡ (λ x → h (hInv (c x)))

   ι f c = ap (λ - → - ∘ c)(EpicInvIsRightInv gfe h hEpi)⁻¹

   useker : (f : ∣ 𝑆 ∣)  (c : ∥ 𝑆 ∥ f → C)
    → g (hInv (h (FA f (hInv ∘ c)))) ≡ g(FA f (hInv ∘ c))

   useker = λ f c
    → Kh⊆Kg (cong-app
             (EpicInvIsRightInv gfe h hEpi)
             (h(FA f(hInv ∘ c)))
            )

   ϕIsHomCB : (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → C) → ϕ (FC f a) ≡ FB f (ϕ ∘ a)

   ϕIsHomCB f c =
    g (hInv (FC f c))               ≡⟨ i   ⟩
    g (hInv (FC f (h ∘ (hInv ∘ c)))) ≡⟨ ii  ⟩
    g (hInv (h (FA f (hInv ∘ c))))   ≡⟨ iii ⟩
    g (FA f (hInv ∘ c))              ≡⟨ iv  ⟩
    FB f (λ x → g (hInv (c x)))      ∎
    where
     i   = ap (g ∘ hInv) (ap (FC f) (ι f c))
     ii  = ap (λ - → g (hInv -)) (hhom f (hInv ∘ c))⁻¹
     iii = useker f c
     iv  = ghom f (hInv ∘ c)

-->
