--FILE: closure.lagda.rst
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 2 Jul 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext; dfunext; fst; snd)

module closure
 {𝑆 : Signature 𝓞 𝓥}
 {X : 𝓤 ̇ }
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {𝕏 : (𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨} where

open import homomorphisms {𝑆 = 𝑆} public
open import terms {𝑆 = 𝑆} public
open import subuniverses {𝑆 = 𝑆} public
open import congruences public

_⊧_≈_ : Algebra 𝓤 𝑆
 →      Term{X = X} → Term → 𝓤 ̇

𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : Pred (Algebra 𝓤 𝑆) 𝓦
 →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇

_⊧_≋_ 𝒦 p q = {𝑨 : Algebra _ 𝑆} → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

----------------------------------------------------------------------
--Closure under products
data PClo (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 pbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ PClo 𝒦
 prod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆}
  →     (∀ i → 𝒜 i ∈ PClo 𝒦)
  →     ⨅ 𝒜 ∈ PClo 𝒦

P-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺ ))
 →      (𝓘 : Universe) (I : 𝓘 ̇ ) (𝒜 : I → Algebra 𝓘 𝑆)
 →      (( i : I ) → 𝒜 i ∈ ℒ𝒦 𝓘 ) → 𝓘 ⁺ ̇
P-closed ℒ𝒦 = λ 𝓘 I 𝒜 𝒜i∈ℒ𝒦 →  ⨅ 𝒜  ∈ (ℒ𝒦 𝓘)

products-preserve-identities :
      (p q : Term{X = X})
      (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →    ((i : I) → (𝒜 i) ⊧ p ≈ q)
     -----------------------------------
 →     ⨅ 𝒜 ⊧ p ≈ q

products-preserve-identities p q I 𝒜 𝒜⊧p≈q = γ
 where
   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = gfe λ a →
    (p ̇ ⨅ 𝒜) a
      ≡⟨ interp-prod gfe p 𝒜 a ⟩
    (λ i → ((p ̇ (𝒜 i)) (λ x → (a x) i)))
      ≡⟨ gfe (λ i → cong-app (𝒜⊧p≈q i) (λ x → (a x) i)) ⟩
    (λ i → ((q ̇ (𝒜 i)) (λ x → (a x) i)))
      ≡⟨ (interp-prod gfe q 𝒜 a)⁻¹ ⟩
    (q ̇ ⨅ 𝒜) a
      ∎

products-in-class-preserve-identities :
     (𝒦 : Pred (Algebra 𝓤 𝑆) ( 𝓤 ⁺ ))
     (p q : Term{X = X})
     (I : 𝓤 ̇ ) (𝒜 : I → Algebra 𝓤 𝑆)
 →   𝒦 ⊧ p ≋ q  →  ((i : I) → 𝒜 i ∈ 𝒦)
     ------------------------------------
 →    ⨅ 𝒜 ⊧ p ≈ q

products-in-class-preserve-identities 𝒦 p q I 𝒜 𝒦⊧p≋q all𝒜i∈𝒦 = γ
 where
   𝒜⊧p≈q : ∀ i → (𝒜 i) ⊧ p ≈ q
   𝒜⊧p≈q i = 𝒦⊧p≋q (all𝒜i∈𝒦 i)

   γ : (p ̇ ⨅ 𝒜) ≡ (q ̇ ⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 𝒜⊧p≈q

----------------------------------------------------------------------
--Closure under subalgebras
data SClo (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
 sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SClo 𝒦

-- data SClo (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
--  sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
--  sub : (SAK : SubalgebrasOfClass 𝒦) → (pr₁ ∥ (pr₂ SAK) ∥) ∈ SClo 𝒦

S-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 𝑆) (𝓤 ⁺))
 →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
S-closed ℒ𝒦 =
 λ 𝓤 B → (B is-subalgebra-of-class (ℒ𝒦 𝓤)) → (B ∈ ℒ𝒦 𝓤)

subalgebras-preserve-identities : (𝒦 : Pred (Algebra 𝓤 𝑆) ( 𝓤 ⁺ ))(p q : Term{X = X})
 →  (𝒦 ⊧ p ≋ q) → (SAK : SubalgebrasOfClass 𝒦)
 →  (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q
subalgebras-preserve-identities 𝒦 p q 𝒦⊧p≋q SAK = γ
 where

  𝑨 : Algebra 𝓤 𝑆
  𝑨 = ∣ SAK ∣

  A∈𝒦 : 𝑨 ∈ 𝒦
  A∈𝒦 = ∣ pr₂ SAK ∣

  A⊧p≈q : 𝑨 ⊧ p ≈ q
  A⊧p≈q = 𝒦⊧p≋q A∈𝒦

  subalg : SubalgebrasOf 𝑨
  subalg = ∥ pr₂ SAK ∥

  𝑩 : Algebra 𝓤 𝑆
  𝑩 = pr₁ subalg

  h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  h = ∣ pr₂ subalg ∣

  hem : is-embedding h
  hem = pr₁ ∥ pr₂ subalg ∥

  hhm : is-homomorphism 𝑩 𝑨 h
  hhm = pr₂ ∥ pr₂ subalg ∥

  ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
  ξ b =
   h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
   (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
   (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
   h ((q ̇ 𝑩) b)  ∎

  hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
  hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

  γ : 𝑩 ⊧ p ≈ q
  γ = gfe λ b → hlc (ξ b)

----------------------------------------------------------------------

--Closure under hom images
data HClo (𝒦 : Pred (Algebra 𝓤 𝑆)(𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ HClo 𝒦
 hhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ HClo 𝒦 → ((𝑩 , _ ) : HomImagesOf 𝑨) → 𝑩 ∈ HClo 𝒦


module _ {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)} where

 -- ⇒ (the "only if" direction)
 identities-compatible-with-homs : (p q : Term{X = X})
  →                𝒦 ⊧ p ≋ q
       ----------------------------------------------------
  →     ∀ 𝑨 KA h → ∣ h ∣ ∘ (p ̇ (𝑻(X))) ≡ ∣ h ∣ ∘ (q ̇ (𝑻(X)))
 -- Here, the inferred types are
 -- 𝑨 : Algebra 𝓤 𝑆, KA : 𝒦 𝑨, h : hom ((𝑻(X))) 𝑨

 identities-compatible-with-homs p q 𝒦⊧p≋q 𝑨 KA h = γ
  where
   pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
   pA≡qA = 𝒦⊧p≋q KA

   pAh≡qAh : ∀(𝒂 : X → ∣ 𝑻(X) ∣ )
    →        (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂)
   pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

   hpa≡hqa : ∀(𝒂 : X → ∣ 𝑻(X) ∣ )
    →        ∣ h ∣ ((p ̇ 𝑻(X)) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻(X)) 𝒂)
   hpa≡hqa 𝒂 =
    ∣ h ∣ ((p ̇ 𝑻(X)) 𝒂)  ≡⟨ comm-hom-term gfe (𝑻 X) 𝑨 h p 𝒂 ⟩
    (p ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
    (q ̇ 𝑨)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 h q 𝒂)⁻¹ ⟩
    ∣ h ∣ ((q ̇ 𝑻(X)) 𝒂)  ∎

   γ : ∣ h ∣ ∘ (p ̇ 𝑻(X)) ≡ ∣ h ∣ ∘ (q ̇ 𝑻(X))
   γ = gfe hpa≡hqa

 -- ⇐ (the "if" direction)
 homs-compatible-with-identities : (p q : Term)
  →    (∀ 𝑨 KA h  →  ∣ h ∣ ∘ (p ̇ 𝑻(X)) ≡ ∣ h ∣ ∘ (q ̇ 𝑻(X)))
       --------------------------------------------------
  →                𝒦 ⊧ p ≋ q
 --inferred types: 𝑨 : Algebra 𝓤 𝑆, KA : 𝑨 ∈ 𝒦, h : hom (𝑻(X)) 𝑨

 homs-compatible-with-identities p q all-hp≡hq {𝑨} KA = γ
  where
   h : (𝒂 : X → ∣ 𝑨 ∣) → hom (𝑻 X) 𝑨
   h 𝒂 = lift-hom{𝑨 = 𝑨} 𝒂

   γ : 𝑨 ⊧ p ≈ q
   γ = gfe λ 𝒂 →
    (p ̇ 𝑨) 𝒂
      ≡⟨ refl _ ⟩
    (p ̇ 𝑨)(∣ h 𝒂 ∣ ∘ generator)
      ≡⟨(comm-hom-term gfe (𝑻 X) 𝑨 (h 𝒂) p generator)⁻¹ ⟩
    (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻(X))) generator
      ≡⟨ ap (λ - → - generator) (all-hp≡hq 𝑨 KA (h 𝒂)) ⟩
    (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻(X))) generator
      ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 (h 𝒂) q generator) ⟩
    (q ̇ 𝑨)(∣ h 𝒂 ∣ ∘ generator)
      ≡⟨ refl _ ⟩
    (q ̇ 𝑨) 𝒂
      ∎

 compatibility-of-identities-and-homs : (p q : Term)
  →  (𝒦 ⊧ p ≋ q)
      ⇔ (∀ 𝑨 ka hh → ∣ hh ∣ ∘ (p ̇ 𝑻(X)) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻(X)))
 --inferred types: 𝑨 : algebra 𝓤 s, ka : 𝑨 ∈ 𝒦, hh : hom (𝑻(X)) 𝑨.

 compatibility-of-identities-and-homs p q =
   identities-compatible-with-homs p q ,
   homs-compatible-with-identities p q

 --Compatibility of identities with interpretation of terms
 compatibility-of-interpretations : (p q : Term)
  →        (𝒦 ⊧ p ≋ q)
  →        ∀ 𝑨 (ka : 𝑨 ∈ 𝒦) (hh : hom (𝑻 X) 𝑨)
  →        ∣ hh ∣ ((∣ term-gen{gfe = gfe} p ∣ ̇ 𝑻(X)) generator)
         ≡ ∣ hh ∣ ((∣ term-gen{gfe = gfe} q ∣ ̇ 𝑻(X)) generator)

 compatibility-of-interpretations p q 𝒦⊧p≋q 𝑨 ka hh = γ
  where
   g : X → Term
   g = generator

   tgp : Σ 𝓅 ꞉ ∣ 𝑻(X) ∣ , p ≡ (𝓅 ̇ 𝑻(X)) g
   tgp   = term-gen{gfe = gfe} p

   tgq : Σ 𝓆 ꞉ ∣ 𝑻(X) ∣ , q ≡ (𝓆 ̇ 𝑻(X)) g
   tgq   = term-gen{gfe = gfe} q

   𝓅 𝓆 : ∣ 𝑻 X ∣  -- Notation: 𝓅 = \Mcp
   𝓅 = ∣ tgp ∣
   𝓆 = ∣ tgq ∣

   p≡𝓅 : p ≡ (𝓅 ̇ 𝑻 X) g
   p≡𝓅 = ∥ tgp ∥

   q≡𝓆 : q ≡ (𝓆 ̇ 𝑻 X) g
   q≡𝓆 = ∥ tgq ∥

   pA≡qA : p ̇ 𝑨 ≡ q ̇ 𝑨
   pA≡qA = 𝒦⊧p≋q ka

   γ : ∣ hh ∣ ((𝓅 ̇ 𝑻 X) generator) ≡ ∣ hh ∣ ((𝓆 ̇ 𝑻 X) g)
   γ =
    ∣ hh ∣ ((𝓅 ̇ 𝑻 X) g)  ≡⟨ (ap ∣ hh ∣ (term-gen-agreement p))⁻¹ ⟩
    ∣ hh ∣ ((p ̇ 𝑻 X) g)  ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 hh p g) ⟩
    (p ̇ 𝑨) (∣ hh ∣ ∘ g)  ≡⟨ intensionality pA≡qA (∣ hh ∣ ∘ g)  ⟩
    (q ̇ 𝑨) (∣ hh ∣ ∘ g)  ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑨 hh q g)⁻¹ ⟩
    ∣ hh ∣ ((q ̇ 𝑻 X) g)  ≡⟨ ap ∣ hh ∣ (term-gen-agreement q) ⟩
    ∣ hh ∣ ((𝓆 ̇ 𝑻 X) g)  ∎



 -- The free algebra in Agda
 𝑻HI = HomImagesOf (𝑻 X)

 𝑻img : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
 𝑻img  =  Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) ,
           Σ ϕ ꞉ hom (𝑻 X) 𝑨 , (𝑨 ∈ SClo 𝒦) × Epic ∣ ϕ ∣

 𝑻𝑨 : (ti : 𝑻img) → Algebra 𝓤 𝑆
 𝑻𝑨 ti = ∣ ti ∣

 𝑻𝑨∈SClo𝒦 : (ti : 𝑻img) → (𝑻𝑨 ti) ∈ SClo 𝒦
 𝑻𝑨∈SClo𝒦 ti = ∣ pr₂ ∥ ti ∥ ∣

 𝑻ϕ : (ti : 𝑻img) → hom (𝑻 X) (𝑻𝑨 ti)
 𝑻ϕ ti = pr₁ ∥ ti ∥

 𝑻ϕE : (ti : 𝑻img) → Epic ∣ (𝑻ϕ ti) ∣
 𝑻ϕE ti = ∥ pr₂ ∥ ti ∥ ∥

 𝑻KER : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
 𝑻KER = Σ (p , q) ꞉ (∣ (𝑻 X) ∣ × ∣ (𝑻 X) ∣) ,
   ∀ ti → (p , q) ∈ KER-pred{B = ∣ (𝑻𝑨 ti) ∣} ∣ 𝑻ϕ ti ∣

 Ψ : Pred (∣ (𝑻 X) ∣ × ∣ (𝑻 X) ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
 Ψ (p , q) =
  ∀ ti → ∣ (𝑻ϕ ti) ∣ p ≡ ∣ (𝑻ϕ ti) ∣ q

 Ψ' : Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
 Ψ' p q = ∀ ti → ∣ (𝑻ϕ ti) ∣ p ≡ ∣ (𝑻ϕ ti) ∣ q -- p q = ∀ ti → ∣ (𝑻ϕ ti) ∣ p ≡ ∣ (𝑻ϕ ti) ∣ q

 𝑻img→𝑻⊧ : ∀ p q
  →        (p , q) ∈ Ψ
  →        (ti : 𝑻img)
       -----------------------------------
  →     ∣ (𝑻ϕ ti) ∣ ((p ̇ 𝑻(X)) generator)
      ≡ ∣ (𝑻ϕ ti) ∣ ((q ̇ 𝑻(X)) generator)
 𝑻img→𝑻⊧ p q pΨq ti = goal1
  where
   𝑪 : Algebra 𝓤 𝑆
   𝑪 = ∣ ti ∣

   ϕ : hom (𝑻 X) 𝑪
   ϕ = 𝑻ϕ ti

   pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
   pCq = pΨq ti

   g : X → Term
   g = generator

   𝓅 𝓆 : ∣ 𝑻 X ∣  -- Notation: 𝓅 = \Mcp
   𝓅 = ∣ tg{X = X}{gfe = gfe} p ∣
   𝓆 = ∣ tg{X = X}{gfe = gfe} q ∣

   p≡𝓅 : p ≡ (𝓅 ̇ 𝑻 X) g
   p≡𝓅 = ∥ tg p ∥

   q≡𝓆 : q ≡ (𝓆 ̇ 𝑻 X) g
   q≡𝓆 = ∥ tg q ∥

   ξ : ∣ ϕ ∣ ((𝓅 ̇ 𝑻(X)) g) ≡ ∣ ϕ ∣ ((𝓆 ̇ 𝑻(X)) g)
   ξ = (ap ∣ ϕ ∣ p≡𝓅)⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣ q≡𝓆)

   goal1 : ∣ ϕ ∣ ((p ̇ 𝑻(X)) g) ≡ ∣ ϕ ∣ ((q ̇ 𝑻(X)) g)
   goal1 = (ap ∣ ϕ ∣ (term-gen-agreement p))
            ∙ ξ ∙ (ap ∣ ϕ ∣ (term-gen-agreement q))⁻¹

--N.B. Ψ𝒦𝑻 is the kernel of 𝑻(X) → 𝔽(𝒦, 𝑻(X)).  Therefore, to prove
--𝑨 is a hom image of 𝔽(𝒦, 𝑻(X)), it suffices to show that the kernel of
--the lift h : 𝑻(X) → 𝑨 *contains* Ψ𝒦𝑻
--
--    𝑻---- g --->>𝔽  (ker g = Ψ𝒦𝑻)
--     \         .
--      \       .
--       h     ∃ϕ     (want: Ψ𝒦𝑻 ⊆ ker h)
--        \   .
--         \ .
--          V
--          𝑨
  -- record Congruence (A : Algebra 𝓤 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
  --   constructor mkcon
  --   field
  --     ⟨_⟩ : Rel ∣ A ∣ 𝓤
  --     Compatible : compatible A ⟨_⟩
  --     IsEquiv : IsEquivalence ⟨_⟩
 𝑻compatible-op : ∣ 𝑆 ∣ → Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
  →              𝓥 ⊔ 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
 𝑻compatible-op f R = (lift-rel R) =[ (f ̂ 𝑻(X)) ]⇒ R

 𝑻compatible : Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) ̇
 𝑻compatible R = ∀ f → 𝑻compatible-op f R

 record 𝑻Congruence : (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) ⁺ ̇  where
  constructor mk𝑻con
  field
   ⟨_⟩ : Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
   Compatible : 𝑻compatible ⟨_⟩
   IsEquiv : IsEquivalence ⟨_⟩

 -- Ψ'-𝑻compatible : 𝑻compatible Ψ'
 -- Ψ'-𝑻compatible = {!!}
 -- Ψ'-IsEquiv : IsEquivalence Ψ'
 -- Ψ'-IsEquiv = {!!}
 -- ConΨ : 𝑻Congruence
 -- ConΨ = mk𝑻con Ψ' Ψ'-𝑻compatible Ψ'-IsEquiv

 -- data 𝔽 {X : 𝓤 ̇} :  𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇  where
 --  generator : X → 𝔽 {X = X}
 --  node : (f : ∣ 𝑆 ∣) (args : ∥ 𝑆 ∥ f → 𝔽 {X = X}) → 𝔽
 --  identities : (𝓡 : Rel 𝔽 𝓤) (f g : ∣ 𝑆 ∣)(a1 : ∥ 𝑆 ∥ f → 𝔽 {X = X}) (a2 : ∥ 𝑆 ∥ g → 𝔽)(_ : 𝓡 (node f a1) (node g a2)) → (node f a1) ≡ (node g a2)

 -- ⟪_⟫_ : (t : Term) → Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) ̇
 -- ⟪ t ⟫ R = Σ x ꞉ _ ,  R t x

 -- 𝑻/_ : 𝑻Congruence → Algebra ((𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) ⁺) 𝑆
 -- 𝑻/ θ = ((Σ C ꞉ _ , Σ a ꞉ (𝑻(X)) , C ≡ ( ⟪ a ⟫ θ )) , -- carrier
 --            (λ f args        -- operations
 --             → ⟪ ((f ̂ 𝑻(X))(λ i₁ → ∣ ∥ args i₁ ∥ ∣)) ⟫ ⟨ θ ⟩ ,
 --               ((f ̂ 𝑻(X)) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
 --            )
 --          )
 -- 𝔽 : Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) 𝑆
 -- 𝔽 = (𝑻 X) ╱ ConΨ

-- Variety Closure
data VClo (𝒦 : Pred (Algebra 𝓤 𝑆) (𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
 vbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ VClo 𝒦
 vprod : {I : 𝓤 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → 𝒜 i ∈ VClo 𝒦) → ⨅ 𝒜 ∈ VClo 𝒦
 vsub : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ VClo 𝒦
 vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦





module _ {𝒦 : Pred (Algebra 𝓤 𝑆) ( 𝓤 ⁺ )} where

 pclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (PClo 𝒦 ⊧ p ≋ q)
 pclo-id1 {p} {q} α (pbase x) = α x
 pclo-id1 {p} {q} α (prod{I}{𝒜} 𝒜-P𝒦 ) = γ
  where
   IH : (i : I)  → (p ̇ 𝒜 i) ≡ (q ̇ 𝒜 i)
   IH = λ i → pclo-id1{p}{q} α  ( 𝒜-P𝒦  i )
   γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 pclo-id2 : ∀{p q} → ((PClo 𝒦) ⊧ p ≋ q ) → (𝒦 ⊧ p ≋ q)
 pclo-id2 p A∈𝒦 = p (pbase A∈𝒦)

 sclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (SClo 𝒦 ⊧ p ≋ q)
 sclo-id1 {p} {q} 𝒦⊧p≋q (sbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 sclo-id1 {p} {q} 𝒦⊧p≋q (sub {𝑨 = 𝑨} A∈SClo𝒦 sa) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = sclo-id1{p}{q} 𝒦⊧p≋q A∈SClo𝒦

   B : Algebra 𝓤 𝑆
   B = ∣ sa ∣

   h : ∣ B ∣ → ∣ 𝑨 ∣
   h = pr₁ ∥ sa ∥

   hem : is-embedding h
   hem = ∣ pr₂ ∥ sa ∥ ∣

   hhm : is-homomorphism B 𝑨 h
   hhm = ∥ pr₂ ∥ sa ∥ ∥

   ξ : (b : X → ∣ B ∣ ) → h ((p ̇ B) b) ≡ h ((q ̇ B) b)
   ξ b =
    h ((p ̇ B) b)  ≡⟨ comm-hom-term gfe B 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe B 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ B) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ B ≡ q ̇ B
   γ = gfe λ b → hlc (ξ b)

 sclo-id2 : ∀ {p q} → (SClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 sclo-id2 p A∈𝒦 = p (sbase A∈𝒦)

 hclo-id1 : ∀{p q} → (𝒦 ⊧ p ≋ q) → (HClo 𝒦 ⊧ p ≋ q)
 hclo-id1 {p}{q} 𝒦⊧p≋q (hbase A∈𝒦) = 𝒦⊧p≋q A∈𝒦
 hclo-id1 {p}{q} 𝒦⊧p≋q (hhom{𝑨} A∈HClo𝒦 𝑩ϕhE) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = (hclo-id1{p}{q} 𝒦⊧p≋q ) A∈HClo𝒦

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = ∣ 𝑩ϕhE ∣

   ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
   ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

   ϕhom : is-homomorphism 𝑨 𝑩 ϕ
   ϕhom = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

   ϕsur : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
   ϕsur 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕsur 𝒃 x))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕsur 𝒃 x)

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃 ∎

 hclo-id2 : ∀ {p q} → (HClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 hclo-id2 p A∈𝒦 = p (hbase A∈𝒦)

 vclo-id1 : ∀ {p q} → (𝒦 ⊧ p ≋ q) → (VClo 𝒦 ⊧ p ≋ q)
 vclo-id1 {p} {q} α (vbase A∈𝒦) = α A∈𝒦
 vclo-id1 {p} {q} α (vprod{I = I}{𝒜 = 𝒜} 𝒜∈VClo𝒦) = γ
  where
   IH : (i : I) → 𝒜 i ⊧ p ≈ q
   IH i = vclo-id1{p}{q} α (𝒜∈VClo𝒦 i)

   γ : p ̇ (⨅ 𝒜)  ≡ q ̇ (⨅ 𝒜)
   γ = products-preserve-identities p q I 𝒜 IH

 vclo-id1 {p} {q} α ( vsub {𝑨 = 𝑨} A∈VClo𝒦 sa ) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = ∣ sa ∣

   h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   h = pr₁ ∥ sa ∥

   hem : is-embedding h
   hem = ∣ pr₂ ∥ sa ∥ ∣

   hhm : is-homomorphism 𝑩 𝑨 h
   hhm = ∥ pr₂ ∥ sa ∥ ∥

   ξ : (b : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) b) ≡ h ((q ̇ 𝑩) b)
   ξ b =
    h ((p ̇ 𝑩) b)  ≡⟨ comm-hom-term gfe 𝑩 𝑨 (h , hhm) p b ⟩
    (p ̇ 𝑨)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
    (q ̇ 𝑨)(h ∘ b) ≡⟨ (comm-hom-term gfe 𝑩 𝑨 (h , hhm) q b)⁻¹ ⟩
    h ((q ̇ 𝑩) b)  ∎

   hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
   hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

   γ : p ̇ 𝑩 ≡ q ̇ 𝑩
   γ = gfe λ b → hlc (ξ b)

 vclo-id1 {p}{q} α (vhom{𝑨 = 𝑨} A∈VClo𝒦 𝑩ϕhE) = γ
  where
   A⊧p≈q : 𝑨 ⊧ p ≈ q
   A⊧p≈q = vclo-id1{p}{q} α A∈VClo𝒦

   𝑩 : Algebra 𝓤 𝑆
   𝑩 = ∣ 𝑩ϕhE ∣

   ϕ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
   ϕ = ∣ ∥ 𝑩ϕhE ∥ ∣

   ϕh : is-homomorphism 𝑨 𝑩 ϕ
   ϕh = ∣ pr₂ ∥ 𝑩ϕhE ∥ ∣

   ϕE : (𝒃 : X → ∣ 𝑩 ∣ )(x : X) → Image ϕ ∋ (𝒃 x)
   ϕE 𝒃 x = ∥ pr₂ ∥ 𝑩ϕhE ∥ ∥ (𝒃 x)

   preim : (𝒃 : X → ∣ 𝑩 ∣)(x : X) → ∣ 𝑨 ∣
   preim 𝒃 x = (Inv ϕ (𝒃 x) (ϕE 𝒃 x))

   ζ : (𝒃 : X → ∣ 𝑩 ∣) → ϕ ∘ (preim 𝒃) ≡ 𝒃
   ζ 𝒃 = gfe λ x → InvIsInv ϕ (𝒃 x) (ϕE 𝒃 x)

   γ : (p ̇ 𝑩) ≡ (q ̇ 𝑩)
   γ = gfe λ 𝒃 →
    (p ̇ 𝑩) 𝒃               ≡⟨ (ap (p ̇ 𝑩) (ζ 𝒃))⁻¹ ⟩
    (p ̇ 𝑩) (ϕ ∘ (preim 𝒃)) ≡⟨ (comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
    ϕ((p ̇ 𝑨)(preim 𝒃))     ≡⟨ ap ϕ (intensionality A⊧p≈q (preim 𝒃)) ⟩
    ϕ((q ̇ 𝑨)(preim 𝒃))     ≡⟨ comm-hom-term gfe 𝑨 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
    (q ̇ 𝑩)(ϕ ∘ (preim 𝒃))  ≡⟨ ap (q ̇ 𝑩) (ζ 𝒃) ⟩
    (q ̇ 𝑩) 𝒃 ∎

 vclo-id2 : ∀ {p q} → (VClo 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 vclo-id2 p A∈𝒦 = p (vbase A∈𝒦)


 -- Equational classes
 TH : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → _ ̇
 TH 𝒦 = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝒦 ⊧ p ≋ q

 Th : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺)
 Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

 MOD : (ℰ : Pred (Term{X = X} × Term) 𝓤) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ̇
 MOD ℰ = Σ A ꞉ (Algebra 𝓤 𝑆) , ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

 Mod : Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺) → Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ )
 Mod ℰ = λ A → ∀ p q → (p , q) ∈ ℰ → A ⊧ p ≈ q

 -- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
 ThHSP-axiomatizes : (p q : ∣ (𝑻 X) ∣)
           -----------------------------------------
  →         𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th (VClo 𝒦))

 ThHSP-axiomatizes p q =
  (λ 𝒦⊧p≋q 𝑨∈VClo𝒦 → vclo-id1{p = p}{q = q} 𝒦⊧p≋q 𝑨∈VClo𝒦) ,
   λ pq∈Th 𝑨∈𝒦 → pq∈Th (vbase 𝑨∈𝒦)


 -- pq∈ : ∀{p}{q} → (p , q) ∈ Ψ{𝒦} → (p , q) ∈ Th (VClo 𝒦)
 -- pq∈ {p} {q} pΨq {𝑪} 𝑪∈VClo𝒦 = {!γ!}
 --  where

 --   ℊ : X → Term
 --   ℊ = generator

 --   ℋ : X ↠ 𝑪
 --   ℋ = 𝕏 𝑪

 --   h₀ : X → ∣ 𝑪 ∣
 --   h₀ = fst ℋ

 --   hE : Epic h₀
 --   hE = snd ℋ

 --   h : hom (𝑻 X) 𝑪
 --   h = lift-hom{𝑨 = 𝑪}{X = X} h₀

 --   ti : 𝑻img
 --   ti = 𝑪 , h , (sbase 𝑪∈VClo𝒦 , lift-of-epic-is-epic h₀ hE )

 --   pCq : ∣ h ∣ p ≡ ∣ h ∣ q
 --   pCq = pΨq ti

 --   pCp : (p : Term) → ∣ h ∣ p ≡ (p ̇ 𝑪) h₀
 --   pCp p = ξ
 --    where
 --     tg𝓅 : Σ 𝓅 ꞉ ∣ 𝑻(X) ∣ , p ≡ (𝓅 ̇ 𝑻(X)) ℊ
 --     tg𝓅 = term-gen{gfe = gfe} p

 --     𝓅 : ∣ (𝑻 X) ∣
 --     𝓅 = ∣ tg𝓅 ∣

 --     tgp : (p ̇ 𝑻(X)) ℊ ≡ (𝓅 ̇ 𝑻(X)) ℊ
 --     tgp = term-gen-agreement p

 --     p≡𝓅 : p ≡ (p ̇ 𝑻(X)) ℊ
 --     p≡𝓅 = ∥ tg𝓅 ∥ ∙ (tgp)⁻¹

 --     ξ : ∣ h ∣ p ≡ (p ̇ 𝑪) h₀
 --     ξ =
 --      ∣ h ∣ p ≡⟨ ap ∣ h ∣ p≡𝓅 ⟩
 --       ∣ h ∣ ((p ̇ 𝑻(X)) ℊ)  ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 h p ℊ ⟩
 --       (p ̇ 𝑪) (∣ h ∣ ∘ ℊ)  ≡⟨ ap (p ̇ 𝑪) (refl _) ⟩
 --       (p ̇ 𝑪) h₀ ∎

 --   i' : (p ̇ 𝑪) h₀ ≡ (q ̇ 𝑪) h₀
 --   i' =
 --    (p ̇ 𝑪) h₀ ≡⟨ (pCp p)⁻¹ ⟩
 --    ∣ h ∣ p     ≡⟨ pCq ⟩
 --    ∣ h ∣ q     ≡⟨ pCp q ⟩
 --    (q ̇ 𝑪) h₀ ∎

 --   agree0 : ∣ h ∣ ((p ̇ 𝑻(X)) ℊ) ≡ ∣ h ∣ ((q ̇ 𝑻(X)) ℊ)
 --   agree0 = 𝑻img→𝑻⊧ p q pΨq ti

 --   preim : (𝒄 : X → ∣ 𝑪 ∣) → X → ∣ (𝑻 X) ∣
 --   preim 𝒄 x = Inv ∣ h ∣ (𝒄 x) ((lift-of-epic-is-epic h₀ hE) (𝒄 x))

 --   agree1 : (𝒕 : X → ∣ (𝑻 X) ∣) → ∣ h ∣ ((p ̇ 𝑻(X)) 𝒕) ≡ ∣ h ∣ ((q ̇ 𝑻(X)) 𝒕)
 --   agree1 𝒕 = {!!}

 --   IInv : (𝒄 : X → ∣ 𝑪 ∣) → ∣ h ∣ ∘ (preim 𝒄) ≡ 𝒄
 --   IInv 𝒄 = gfe λ x → InvIsInv ∣ h ∣ (𝒄 x) ((lift-of-epic-is-epic h₀ hE) (𝒄 x))

 --   γ : 𝑪 ⊧ p ≈ q
 --   γ = gfe λ 𝒄 → {!!}
     -- (p ̇ 𝑪) 𝒄                 ≡⟨ (ap (p ̇ 𝑪) (IInv 𝒄))⁻¹ ⟩
     -- (p ̇ 𝑪) (∣ g ∣ ∘ (preim 𝒄)) ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑪 g p (preim 𝒄))⁻¹ ⟩
     -- ∣ g ∣ ((p ̇ 𝑻(X)) (preim 𝒄)) ≡⟨ agree1 (preim 𝒄) ⟩
     -- ∣ g ∣ ((q ̇ 𝑻(X)) (preim 𝒄)) ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 g q (preim 𝒄) ⟩
     -- (q ̇ 𝑪)(∣ g ∣ ∘ (preim 𝒄))  ≡⟨ ap (q ̇ 𝑪) (IInv 𝒄) ⟩
     -- (q ̇ 𝑪) 𝒄 ∎



 -- pq∈ {p} {q} pΨq (vbase {𝑪} 𝑪∈𝒦) = i
 --  where
 --   ℊ : X → Term
 --   ℊ = generator

 --   ℋ : X ↠ 𝑪
 --   ℋ = 𝕏 𝑪

 --   h₀ : X → ∣ 𝑪 ∣
 --   h₀ = fst ℋ

 --   hE : Epic h₀
 --   hE = snd ℋ

 --   h : hom (𝑻 X) 𝑪
 --   h = lift-hom{𝑨 = 𝑪}{X = X} h₀

 --   ti : 𝑻img
 --   ti = 𝑪 , h , (sbase 𝑪∈𝒦 , lift-of-epic-is-epic h₀ hE )

 --   pCq : ∣ h ∣ p ≡ ∣ h ∣ q
 --   pCq = pΨq ti

 --   pCp : (p : Term) → ∣ h ∣ p ≡ (p ̇ 𝑪) h₀
 --   pCp p = ξ
 --    where
 --     tg𝓅 : Σ 𝓅 ꞉ ∣ 𝑻(X) ∣ , p ≡ (𝓅 ̇ 𝑻(X)) ℊ
 --     tg𝓅 = term-gen{gfe = gfe} p

 --     𝓅 : ∣ (𝑻 X) ∣
 --     𝓅 = ∣ tg𝓅 ∣

 --     tgp : (p ̇ 𝑻(X)) ℊ ≡ (𝓅 ̇ 𝑻(X)) ℊ
 --     tgp = term-gen-agreement p

 --     p≡𝓅 : p ≡ (p ̇ 𝑻(X)) ℊ
 --     p≡𝓅 = ∥ tg𝓅 ∥ ∙ (tgp)⁻¹

 --     ξ : ∣ h ∣ p ≡ (p ̇ 𝑪) h₀
 --     ξ =
 --      ∣ h ∣ p ≡⟨ ap ∣ h ∣ p≡𝓅 ⟩
 --       ∣ h ∣ ((p ̇ 𝑻(X)) ℊ)  ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 h p ℊ ⟩
 --       (p ̇ 𝑪) (∣ h ∣ ∘ ℊ)  ≡⟨ ap (p ̇ 𝑪) (refl _) ⟩
 --       (p ̇ 𝑪) h₀ ∎

 --   i' : (p ̇ 𝑪) h₀ ≡ (q ̇ 𝑪) h₀
 --   i' =
 --    (p ̇ 𝑪) h₀ ≡⟨ (pCp p)⁻¹ ⟩
 --    ∣ h ∣ p     ≡⟨ pCq ⟩
 --    ∣ h ∣ q     ≡⟨ pCp q ⟩
 --    (q ̇ 𝑪) h₀ ∎

 --   agree0 : ∣ h ∣ ((p ̇ 𝑻(X)) ℊ) ≡ ∣ h ∣ ((q ̇ 𝑻(X)) ℊ)
 --   agree0 = 𝑻img→𝑻⊧ p q pΨq ti

 --   preim : (𝒄 : X → ∣ 𝑪 ∣) → X → ∣ (𝑻 X) ∣
 --   preim 𝒄 x = Inv ∣ h ∣ (𝒄 x) ((lift-of-epic-is-epic h₀ hE) (𝒄 x))

 --   agree1 : (𝒕 : X → ∣ (𝑻 X) ∣) → ∣ h ∣ ((p ̇ 𝑻(X)) 𝒕) ≡ ∣ h ∣ ((q ̇ 𝑻(X)) 𝒕)
 --   agree1 𝒕 = {!!}

 --   IInv : (𝒄 : X → ∣ 𝑪 ∣) → ∣ h ∣ ∘ (preim 𝒄) ≡ 𝒄
 --   IInv 𝒄 = gfe λ x → InvIsInv ∣ h ∣ (𝒄 x) ((lift-of-epic-is-epic h₀ hE) (𝒄 x))

 --   i : 𝑪 ⊧ p ≈ q
 --   i = gfe λ 𝒄 → {!!}
 --     -- (p ̇ 𝑪) 𝒄                 ≡⟨ (ap (p ̇ 𝑪) (IInv 𝒄))⁻¹ ⟩
 --     -- (p ̇ 𝑪) (∣ g ∣ ∘ (preim 𝒄)) ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑪 g p (preim 𝒄))⁻¹ ⟩
 --     -- ∣ g ∣ ((p ̇ 𝑻(X)) (preim 𝒄)) ≡⟨ agree1 (preim 𝒄) ⟩
 --     -- ∣ g ∣ ((q ̇ 𝑻(X)) (preim 𝒄)) ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 g q (preim 𝒄) ⟩
 --     -- (q ̇ 𝑪)(∣ g ∣ ∘ (preim 𝒄))  ≡⟨ ap (q ̇ 𝑪) (IInv 𝒄) ⟩
 --     -- (q ̇ 𝑪) 𝒄 ∎

 -- pq∈ {p} {q} pΨq (vprod{I}{𝒜} allK𝒜i)  = ii
 --  where
 --   ii : ⨅ 𝒜 ⊧ p ≈ q
 --   ii = {!!}

 -- pq∈ {p} {q} pΨq (vsub{𝑨} 𝑨∈VClo𝒦 SAK) = iii
 --  where
 --   iii : ∣ SAK ∣ ⊧ p ≈ q
 --   iii = {!!}

 -- pq∈ {p} {q} pΨq (vhom {𝑨} 𝑨∈VClo𝒦 BH) = iv
 --  where
 --   iv : ∣ BH ∣ ⊧ p ≈ q
 --   iv = {!!}

