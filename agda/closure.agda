--FILE: closure.lagda.rst
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 2 Jul 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Π'; Op)
open import subuniverses using (Subuniverses; SubunivAlg; hom-image-alg; _is-subalgebra-of_; Subalgebra)
open import homomorphisms using (hom; is-homomorphism)
open import terms using (Term; generator; node; _̇_; _̂_; interp-prod2; interp-prod; comm-hom-term')

module closure {S : Signature 𝓞 𝓥} where

_⊧_≈_ : {X : 𝓧 ̇ } → Algebra 𝓤 S
 →      Term{X = X} → Term → 𝓧 ⊔ 𝓤 ̇

𝑨 ⊧ p ≈ q = (p ̇ 𝑨) ≡ (q ̇ 𝑨)

_⊧_≋_ : {X : 𝓧 ̇ } → Pred (Algebra 𝓤 S) 𝓦
 →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇

_⊧_≋_ 𝓚 p q = {A : Algebra _ S} → 𝓚 A → A ⊧ p ≈ q

𝑷-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ))
 →      (𝓘 : Universe) (I : 𝓘 ̇ ) (𝓐 : I → Algebra 𝓘 S)
 →      (( i : I ) → 𝓐 i ∈ 𝓛𝓚 𝓘 ) → 𝓘 ⁺ ̇
𝑷-closed 𝓛𝓚 = λ 𝓘 I 𝓐 𝓐i∈𝓛𝓚 →  Π' 𝓐  ∈ (𝓛𝓚 𝓘)

module _
 (gfe : global-dfunext)
 (𝓚 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
 {X : 𝓧 ̇ } where

 products-preserve-identities : (p q : Term{X = X})
       (I : 𝓤 ̇ ) (𝓐 : I → Algebra 𝓤 S)
  →    𝓚 ⊧ p ≋ q  →  ((i : I) → 𝓐 i ∈ 𝓚)
  →    Π' 𝓐 ⊧ p ≈ q
 products-preserve-identities p q I 𝓐 𝓚⊧p≋q all𝓐i∈𝓚 = γ
  where
   all𝓐⊧p≈q : ∀ i → (𝓐 i) ⊧ p ≈ q
   all𝓐⊧p≈q i = 𝓚⊧p≋q (all𝓐i∈𝓚 i)

   γ : (p ̇ Π' 𝓐) ≡ (q ̇ Π' 𝓐)
   γ = gfe λ 𝒂 →
    (p ̇ Π' 𝓐) 𝒂
      ≡⟨ interp-prod gfe p 𝓐 𝒂 ⟩
    (λ i → ((p ̇ (𝓐 i)) (λ x → (𝒂 x) i)))
      ≡⟨ gfe (λ i → cong-app (all𝓐⊧p≈q i) (λ x → (𝒂 x) i)) ⟩
    (λ i → ((q ̇ (𝓐 i)) (λ x → (𝒂 x) i)))
      ≡⟨ (interp-prod gfe q 𝓐 𝒂)⁻¹ ⟩
    (q ̇ Π' 𝓐) 𝒂
      ∎

_is-subalgebra-of-class_ : {𝓤 : Universe}(𝑩 : Algebra 𝓤 S)
 →            Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
𝑩 is-subalgebra-of-class 𝓚 =
   Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × (𝑩 is-subalgebra-of 𝑨)

module _
 (𝓚 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ))
 (𝓚' : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))){X : 𝓧 ̇ }
 (𝓤★ : Univalence) where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext 𝓤★

 SubalgebrasOfClass : Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 SubalgebrasOfClass 𝓚 =
  Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × Subalgebra{𝑨 = 𝑨} 𝓤★

 𝑺-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
  →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 𝑺-closed 𝓛𝓚 =
  λ 𝓤 𝑩 → (𝑩 is-subalgebra-of-class (𝓛𝓚 𝓤)) → (𝑩 ∈ 𝓛𝓚 𝓤)

 subalgebras-preserve-identities : (p q : Term{X = X})
  →  (𝓚 ⊧ p ≋ q) → (SAK : SubalgebrasOfClass 𝓚)
  →  (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q
 subalgebras-preserve-identities p q 𝓚⊧p≋q SAK = γ
  where

  𝑨 : Algebra 𝓤 S
  𝑨 = ∣ SAK ∣

  𝑨∈𝓚 : 𝑨 ∈ 𝓚
  𝑨∈𝓚 = ∣ pr₂ SAK ∣

  𝑨⊧p≈q : 𝑨 ⊧ p ≈ q
  𝑨⊧p≈q = 𝓚⊧p≋q 𝑨∈𝓚

  subalg : Subalgebra{𝑨 = 𝑨} 𝓤★
  subalg = ∥ pr₂ SAK ∥

  𝑩 : Algebra 𝓤 S
  𝑩 = pr₁ subalg

  h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  h = ∣ pr₂ subalg ∣

  h-emb : is-embedding h
  h-emb = pr₁ ∥ pr₂ subalg ∥

  h-hom : is-homomorphism 𝑩 𝑨 h
  h-hom = pr₂ ∥ pr₂ subalg ∥

  ξ : (𝒃 : X → ∣ 𝑩 ∣ ) → h ((p ̇ 𝑩) 𝒃) ≡ h ((q ̇ 𝑩) 𝒃)
  ξ 𝒃 =
   h ((p ̇ 𝑩) 𝒃)  ≡⟨ comm-hom-term' gfe 𝑩 𝑨 (h , h-hom) p 𝒃 ⟩
   (p ̇ 𝑨)(h ∘ 𝒃) ≡⟨ intensionality 𝑨⊧p≈q (h ∘ 𝒃) ⟩
   (q ̇ 𝑨)(h ∘ 𝒃) ≡⟨ (comm-hom-term' gfe 𝑩 𝑨 (h , h-hom) q 𝒃)⁻¹ ⟩
   h ((q ̇ 𝑩) 𝒃)  ∎

  hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
  hlc hb≡hb' = (embeddings-are-lc h h-emb) hb≡hb'

  γ : 𝑩 ⊧ p ≈ q
  γ = gfe λ 𝒃 → hlc (ξ 𝒃)


-- Product Closure
data PClo (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
 pbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ PClo 𝓚
 prod : {I : 𝓤 ̇ }{𝓐 : I → Algebra _ S}
  →     (∀ i → 𝓐 i ∈ PClo 𝓚)
  →     Π' 𝓐 ∈ PClo 𝓚

-- Subalgebra Closure
data SClo (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
 sbase : {𝑨 : Algebra _ S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ SClo 𝓚
 --sub : {𝑨 𝑩 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ SClo 𝓚
 --sub : {𝑨 : Algebra _ S} → 𝑨 ∈ SClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ SClo 𝓚
 sub : {𝑨 : Algebra _ S} {B : Pred ∣ 𝑨 ∣ 𝓤 }
       {𝐹 : (𝓸 : ∣ S ∣) → Op (∥ S ∥ 𝓸) (Σ B)}
       (B∈SubA : B ∈ Subuniverses 𝑨)
  →    𝑨 ∈ SClo 𝓚
  →    SubunivAlg{𝑨 = 𝑨}{B = B}{𝐹 = 𝐹} B∈SubA ∈ SClo 𝓚

-- Homomorphic Image Closure
data HClo (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
 hbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ HClo 𝓚
 hhom : {𝑨 𝑩 : Algebra 𝓤 S}{f : hom 𝑨 𝑩}
  →     𝑨 ∈ HClo 𝓚
  →     hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ HClo 𝓚

-- Variety Closure
data VClo (𝓚 : Pred (Algebra 𝓤 S) 𝓣) : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓤 ⁺ ) where
 vbase : {𝑨 : Algebra 𝓤 S} → 𝑨 ∈ 𝓚 → 𝑨 ∈ VClo 𝓚
 vprod : {I : 𝓤 ̇ }{𝓐 : I → Algebra _ S} → (∀ i → 𝓐 i ∈ VClo 𝓚) → Π' 𝓐 ∈ VClo 𝓚
 vsub : ∀{𝑨 : Algebra _ S}{𝑩 : Algebra _ S} → 𝑨 ∈ VClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ VClo 𝓚
 vhom : {𝑨 𝑩 : Algebra 𝓤 S}{f : hom 𝑨 𝑩}
  →     𝑨 ∈ VClo 𝓚 → hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ VClo 𝓚

module _
 (𝓚 : Pred (Algebra 𝓤 S) 𝓣)
 (gfe : global-dfunext)
 (dfe : dfunext 𝓤 𝓤)
 {X : 𝓤 ̇ } where

 _⊧'_≋_ : Pred (Algebra 𝓤 S) 𝓦 → Term {X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇
 _⊧'_≋_ = _⊧_≋_ {X = X}

 pclo-id1 : ∀ {p q} → (𝓚 ⊧ p ≋ q) → (PClo 𝓚 ⊧ p ≋ q)
 pclo-id1 {p} {q} α (pbase x) = α x
 pclo-id1 {p} {q} α (prod{I}{𝓐} 𝓐-P𝓚 ) = γ
  where
   IH : (i : I)  → (p ̇ 𝓐 i) ≡ (q ̇ 𝓐 i)
   IH = λ i → pclo-id1{p}{q} α  ( 𝓐-P𝓚  i )
   γ : p ̇ (Π' 𝓐)  ≡ q ̇ (Π' 𝓐)
   γ =
    (p ̇ (Π' 𝓐) )
     ≡⟨ interp-prod2 gfe p 𝓐 ⟩
    (λ (args : X → ∣ Π' 𝓐 ∣) → (λ i → (p ̇ 𝓐 i)(λ x → (args x) i)))
     ≡⟨ dfe (λ args → (ap (λ - → (λ i → (- i)(λ x → args x i))) (dfe IH))) ⟩
    (λ (args : X → ∣ Π' 𝓐 ∣) → (λ i → (q ̇ 𝓐 i)(λ x → (args x) i)))
     ≡⟨ (interp-prod2 gfe q 𝓐)⁻¹ ⟩
    (q ̇ (Π' 𝓐))
     ∎

 pclo-id2 : ∀{p q} → ((PClo 𝓚) ⊧' p ≋ q ) → (𝓚 ⊧ p ≋ q)
 pclo-id2 p 𝑨∈𝓚 = p (pbase 𝑨∈𝓚)

 sclo-id1 : ∀{p q} → (𝓚 ⊧' p ≋ q) → (SClo 𝓚 ⊧ p ≋ q)
 sclo-id1 {p} {q} 𝓚⊧p≋q (sbase A∈𝓚) = 𝓚⊧p≋q A∈𝓚
 sclo-id1 {p} {q} 𝓚⊧p≋q (sub {𝑨 = 𝑨}{B = B}{𝐹 = 𝐹} B∈SubA A∈SClo𝓚) = γ
  where
   IH : p ̇ 𝑨 ≡ q ̇ 𝑨
   IH = sclo-id1{p}{q} 𝓚⊧p≋q A∈SClo𝓚

   𝑩 : Algebra 𝓤 S
   𝑩 = SubunivAlg{𝑨 = 𝑨}{B = B}{𝐹 = 𝐹} B∈SubA
   -- We need to do this so that both A and Σ B , 𝐹 can be classified by the same predicate SClo.
   -- tB≡tA : ∀ 𝒕 → ( 𝒃 : X → Σ B ) → ( 𝒕 ̇ (Σ B , 𝐹) )( λ x →  𝒃 x ) ≡ (𝒕 ̇ 𝑨) (λ x →  ∣ 𝒃 x ∣ )
   -- tB≡tA 𝒕 = ?
    -- mem :   {B : Pred ∣ 𝑨 ∣ 𝓤}  { 𝐹 : ( 𝓸 : ∣ S ∣ ) → Op ( ∥ S ∥ 𝓸 ) (Σ B) }
    --   →    ( ( 𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → Σ B )  →  ∣ 𝐹 𝓸 𝒂 ∣ ≡ ∥ 𝑨 ∥ 𝓸 (λ i → ∣ 𝒂 i ∣ ) )
    --   →    𝑨 is-supalgebra-of (Σ B , 𝐹)
   uni2alg : 𝑩 is-subalgebra-of 𝑨
   uni2alg = {!!}

   γ : p ̇ 𝑩 ≡ q ̇ 𝑩
   γ = let sts = uni2alg in
    gfe λ 𝒃 →
     (p ̇ 𝑩) 𝒃 ≡⟨ {!!} ⟩  -- we need an elimination rule here (see is-subalg-elim in UF-Subuniverse.agda)
       -- (p ̇ uni2alg) 𝒃 ≡⟨ IH ⟩
       -- (q ̇ uni2alg) 𝒃 ≡⟨ ? ⟩
     (q ̇ 𝑩) 𝒃  ∎

 sclo-id2 : ∀ {p q} → (SClo 𝓚 ⊧' p ≋ q) → (𝓚 ⊧ p ≋ q)
 sclo-id2 p 𝑨∈𝓚 = p (sbase 𝑨∈𝓚)

 hclo-id1 : ∀{p q} → (𝓚 ⊧ p ≋ q) → (HClo 𝓚 ⊧ p ≋ q)
 hclo-id1 {p}{q} 𝓚⊧p≋q (hbase A∈𝓚) = 𝓚⊧p≋q A∈𝓚
 hclo-id1 {p}{q} 𝓚⊧p≋q (hhom{A}{B}{f} A∈HClo𝓚) = γ
  where
   A⊧p≈q : A ⊧ p ≈ q
   A⊧p≈q = (hclo-id1{p}{q} 𝓚⊧p≋q ) A∈HClo𝓚

   IH : (p ̇ A) ≡ (q ̇ A)
   IH = A⊧p≈q

   HIA = hom-image-alg{𝑨 = A}{𝑩 = B} f

   𝒂 : (𝒃 : X → Σ (Image_∋_ ∣ f ∣))(x : X) → ∣ A ∣
   𝒂 = λ 𝒃 x → (Inv ∣ f ∣ (∣ 𝒃 x ∣)(∥ 𝒃 x ∥))

   hom-image-term-interpretation hiti : (𝒃 : X → ∣ HIA ∣)(p : Term)
    → (p ̇ HIA ) 𝒃 ≡ ∣ f ∣ ((p ̇ A)( λ i → 𝒂 𝒃 i )) , im ((p ̇ A)(λ i → 𝒂 𝒃 i))

   hom-image-term-interpretation 𝒃 (generator x) =
    let iiif = ( InvIsInv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥ )⁻¹ in
     𝒃 x ≡⟨ {!!} ⟩ ∣ f ∣ (𝒂 𝒃 x) , im (𝒂 𝒃 x) ∎

   hom-image-term-interpretation 𝒃 (node 𝓸 𝒕) =  ap (λ - → (𝓸 ̂ HIA) -) (gfe λ x → φIH x)
    where
     φIH : (x : ∥ S ∥ 𝓸)
      → ( 𝒕 x ̇ HIA ) 𝒃  ≡ ∣ f ∣ ( ( 𝒕 x ̇ A ) (𝒂 𝒃) ) , im ((𝒕 x ̇ A) (𝒂 𝒃 ) )
     φIH x = hom-image-term-interpretation 𝒃 (𝒕 x)

   hiti = hom-image-term-interpretation  -- alias

   γ : (p ̇ HIA) ≡ (q ̇ HIA)
   γ = (p ̇ HIA)
             ≡⟨ refl _ ⟩
         ( λ ( 𝒃 : X → ∣ HIA ∣ ) → (p ̇ HIA) ( λ x → (𝒃 x) ) )
             ≡⟨ gfe (λ x → hiti x p) ⟩
         ( λ 𝒃 → ∣ f ∣ ( (p ̇ A) ( λ x → 𝒂 𝒃 x ) ) , im ( (p ̇ A) ( λ x → 𝒂 𝒃 x ) ) )
             ≡⟨ ap (λ - → λ 𝒃 → ∣ f ∣ (- (λ x → 𝒂 𝒃 x) )  , im (-  (λ x → 𝒂 𝒃 x) )) IH ⟩
         ( λ 𝒃 → ∣ f ∣ ( (q ̇ A) ( λ x → 𝒂 𝒃 x ) ) , im ( (q ̇ A) ( λ x → 𝒂 𝒃 x ) ) )
             ≡⟨ ( gfe (λ x → hiti x q) )⁻¹ ⟩
         ( λ 𝒃 → (q ̇ HIA) ( λ x → (𝒃 x) ) )
             ≡⟨ refl _ ⟩
         (q ̇ HIA)    ∎

 --   postulate
 --     homclo-id2 : ∀ {p q} → {𝑨 : Algebra k S} → (h : Hom 𝔉 𝑨) → ∣ h ∣ p ≡ ∣ h ∣ q → 𝓚 ⊧ p ≋ q
 hclo-id2 : ∀ {p q} → (HClo 𝓚 ⊧' p ≋ q) → (𝓚 ⊧ p ≋ q)
 hclo-id2 p 𝑨∈𝓚 = p (hbase 𝑨∈𝓚)

 vclo-id1 : ∀ {p q} → (𝓚 ⊧' p ≋ q) → (VClo 𝓚 ⊧ p ≋ q)
 vclo-id1 {p} {q} α (vbase A∈𝓚) = α A∈𝓚
 vclo-id1 {p} {q} α (vprod{I = I}{𝓐 = 𝓐} allAi∈VClo𝓚) = γ
   where
    IH : (i : I) → 𝓐 i ⊧ p ≈ q
    IH i = vclo-id1{p}{q} α (allAi∈VClo𝓚 i)

    γ : p ̇ (Π' 𝓐)  ≡ q ̇ (Π' 𝓐)
    γ =
     (p ̇ (Π' 𝓐))
       ≡⟨ interp-prod2 gfe p 𝓐 ⟩
     (λ (args : X → ∣ Π' 𝓐 ∣) → (λ i → (p ̇ 𝓐 i)(λ x → (args x) i)))
       ≡⟨ dfe (λ args → (ap (λ - → (λ i → (- i)(λ x → args x i))) (dfe IH))) ⟩
     (λ (args : X → ∣ Π' 𝓐 ∣) → (λ i → (q ̇ 𝓐 i)(λ x → (args x) i)))
       ≡⟨ (interp-prod2 gfe q 𝓐)⁻¹ ⟩
     (q ̇ (Π' 𝓐))
       ∎

 --vsub : ∀ {𝑨 : Algebra _ S} {𝑩 : Algebra _ S} → 𝑨 ∈ VClo 𝓚 → 𝑩 is-subalgebra-of 𝑨 → 𝑩 ∈ VClo 𝓚
 vclo-id1 {p} {q} α ( vsub {𝑨 = A}{𝑩 = B} A∈VClo𝓚 B≤A ) = γ
   where
    γ : B ⊧ p ≈ q
    γ = {!!}

 --vhom : {𝑨 𝑩 : Algebra 𝓤 S} {f : Hom 𝑨 𝑩} → 𝑨 ∈ VClo 𝓚 →  hom-image-alg {𝑨 = 𝑨}{𝑩 = 𝑩} f ∈ VClo 𝓚
 vclo-id1 {p} {q} α ( vhom{𝑨 = A}{𝑩 = B}{f = f} 𝑨∈VClo𝓚 ) = γ
   where
    γ : hom-image-alg{𝑨 = A}{𝑩 = B} f ⊧ p ≈ q
    γ = {!!}

 vclo-id2 : ∀ {p q} → (VClo 𝓚 ⊧' p ≋ q) → (𝓚 ⊧ p ≋ q)
 vclo-id2 p 𝑨∈𝓚 = p (vbase 𝑨∈𝓚)

 -- sclo-id1 {generator x} {generator x₁} α (sub {𝑨} {.(Σ _ , _)} (sbase x₂) (mem B≤𝑨 )) = γ
 --   where
 --     γ : ((generator x) ̇ (Σ _ , _)) ≡ ((generator x₁) ̇ (Σ _ , _) )
 --     γ =  (λ 𝒂 → 𝒂 x) ≡⟨ {!!}  ⟩
 --            (λ 𝒂 → 𝒂 x₁) ∎

 -- sclo-id1 {generator x} {generator x₁} α (sub {𝑨} {.(Σ _ , _)} (sub x₂ x₃) (mem B≤𝑨)) = γ
 --   where
 --     γ : ((generator x) ̇ (Σ _ , _)) ≡ ((generator x₁) ̇ (Σ _ , _) )
 --     γ =  (λ 𝒂 → 𝒂 x) ≡⟨ {!!}  ⟩
 --            (λ 𝒂 → 𝒂 x₁) ∎

 -- sclo-id1 {generator x} {node 𝓸 𝒕} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
 --   where
 --     γ : ((generator x) ̇ (Σ _ , _)) ≡ ((node 𝓸 𝒕) ̇ (Σ _ , _) )
 --     γ =  ( λ 𝒂 → 𝒂 x ) ≡⟨ {!!} ⟩
 --           ( λ 𝒂 → (𝓸 ̂ (Σ _ , _) ) (λ x₁ → (𝒕 x₁ ̇ (Σ _ , _) ) 𝒂) )   ∎

 -- sclo-id1 {node 𝓸 𝒕} {generator x} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
 --   where
 --     γ : ((node 𝓸 𝒕) ̇ (Σ _ , _)) ≡ ((generator x) ̇ (Σ _ , _) )
 --     γ = ( ( λ 𝒂 → 𝒂 x ) ≡⟨ {!!} ⟩
 --            ( λ 𝒂 → (𝓸 ̂ (Σ _ , _) ) (λ x₁ → (𝒕 x₁ ̇ (Σ _ , _) ) 𝒂) )   ∎ ) ⁻¹

 -- sclo-id1 {node 𝓸 𝒕} {node 𝓸₁ 𝒕₁} α (sub {𝑨} {.(Σ _ , _)} 𝑨∈SClo𝓚 (mem B≤𝑨)) = γ
 --   where
 --     γ : ((node 𝓸 𝒕) ̇ (Σ _ , _)) ≡ ((node 𝓸₁ 𝒕₁) ̇ (Σ _ , _) )
 --     γ = {!!}
