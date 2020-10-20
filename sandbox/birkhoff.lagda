\begin{code}
--FILE: birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 30 Jun 2020
--REF: Based on the file `birkhoff.agda` (23 Jan 2020).

-- {-# OPTIONS --without-K --exact-split --safe #-}
{-# OPTIONS --without-K --exact-split #-}

open import basic
open import congruences
open import prelude using (global-dfunext; dfunext; funext; Pred; _↪_)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}
 {𝓦 : Universe}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {gfe : global-dfunext}
 {dfe : dfunext 𝓤 𝓤}
 {fevu : dfunext 𝓥 𝓤} where

open import closure {𝑆 = 𝑆}{𝓦 = 𝓦}{𝕏 = 𝕏}{gfe = gfe}{dfe = dfe}{fevu = fevu}

--Equalizers of functions
𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
𝑬 g h x = g x ≡ h x

--Equalizers of homomorphisms
𝑬𝑯 : {𝑨 𝑩 : Algebra 𝓤 𝑆} (g h : hom 𝑨 𝑩) → Pred ∣ 𝑨 ∣ 𝓤
𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x

𝑬𝑯-is-closed : funext 𝓥 𝓤
 →     {𝑓 : ∣ 𝑆 ∣ } {𝑨 𝑩 : Algebra 𝓤 𝑆}
       (g h : hom 𝑨 𝑩)  (𝒂 : (∥ 𝑆 ∥ 𝑓) → ∣ 𝑨 ∣)
 →     ((x : ∥ 𝑆 ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {𝑨 = 𝑨}{𝑩 = 𝑩} g h))
       --------------------------------------------------
 →      ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂) ≡ ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)

𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 p =
   (∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂))    ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
   (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂)  ≡⟨ ap (_ ̂ 𝑩)(fe p) ⟩
   (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)  ≡⟨ (∥ h ∥ 𝑓 𝒂)⁻¹ ⟩
   ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂)    ∎

-- Equalizer of homs is a subuniverse.
𝑬𝑯-is-subuniverse : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}

𝑬𝑯-is-subuniverse fe {𝑨} {𝑩} g h = mksub (𝑬𝑯 {𝑨}{𝑩} g h) λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 x

HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
            (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →          (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
            ---------------------------------------------
 →          (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x

HomUnique fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )    ∎
 where induction-hypothesis = λ x → HomUnique fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

---------------------------
--The free algebra in Agda
---------------------------

𝑻img : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)} → _ ̇
𝑻img {𝓠}{𝓧}{X}{𝒦} = Σ 𝑨 ꞉ (Algebra _ 𝑆) , Σ ϕ ꞉ hom (𝑻{𝓧}{X}) 𝑨 , (𝑨 ∈ SClo 𝒦) × Epic ∣ ϕ ∣

mkti : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
       (𝑨 : Algebra 𝓠 𝑆) → 𝑨 ∈ SClo{𝓤 = 𝓠} 𝒦 → 𝑻img
mkti {𝓠}{𝓧}{X}{𝒦} 𝑨 SCloA = (𝑨 , fst thg , SCloA , snd thg)
 where
  thg : Σ h ꞉ (hom (𝑻{𝓧}{X}) 𝑨), Epic ∣ h ∣
  thg = 𝑻hom-gen 𝑨

𝑻𝑨 : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →   𝑻img{𝓠}{𝓧}{X}{𝒦} → Algebra _ 𝑆
𝑻𝑨 ti = ∣ ti ∣

𝑻ϕ : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
     (ti : 𝑻img{𝓠}{𝓧}{X}{𝒦}) → hom (𝑻{𝓧}{X}) (𝑻𝑨 ti)
𝑻ϕ ti = fst (snd ti)

𝑻ϕE : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
      (ti : 𝑻img{𝓠}{𝓧}{X}{𝒦}) → Epic ∣ 𝑻ϕ ti ∣
𝑻ϕE ti = snd (snd ∥ ti ∥)

𝑻KER : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)} → _ ̇
𝑻KER {𝓠}{𝓧}{X}{𝒦} = Σ (p , q) ꞉ (∣ 𝑻{𝓧}{X} ∣ × ∣ 𝑻 ∣) ,
         ∀ 𝑨 → (SCloA : 𝑨 ∈ SClo 𝒦) → (p , q) ∈ KER-pred{B = ∣ 𝑨 ∣} ∣ 𝑻ϕ (mkti 𝑨 SCloA) ∣

Ψ : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →  Pred (∣ 𝑻{𝓧}{X} ∣ × ∣ 𝑻 ∣) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ⊔ 𝓧 ⁺)
Ψ {𝓠}{𝓧}{X}{𝒦} (p , q) = ∀ (𝑨 : Algebra 𝓠 𝑆) → (SCloA : 𝑨 ∈ SClo{𝓤 = 𝓠} 𝒦)
              → ∣ 𝑻ϕ{𝓠}{𝓧}{X}{𝒦} (mkti 𝑨 SCloA) ∣ ∘ (p ̇ 𝑻) ≡ ∣ 𝑻ϕ (mkti 𝑨 SCloA) ∣ ∘ (q ̇ 𝑻)

ΨRel : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →     Rel ∣ (𝑻{𝓧}{X}) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ⊔ 𝓧 ⁺)
ΨRel {𝓠}{𝓧}{X}{𝒦} p q = Ψ{𝓠}{𝓧}{X}{𝒦} (p , q)

Ψcompatible : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →            compatible{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓦 = (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ⊔ 𝓧 ⁺)} (𝑻{𝓧}{X}) (ΨRel{𝓠}{𝓧}{X}{𝒦})
Ψcompatible {𝓠}{𝓧}{X} f {𝒕} {𝒔} 𝒕Ψ𝒔 𝑨 SCloA = γ
 where
  ϕ : hom 𝑻 𝑨
  ϕ = 𝑻ϕ (mkti 𝑨 SCloA)

  ΨH : ∀ 𝒂 i → (∣ ϕ ∣ ∘ (𝒕 i ̇ 𝑻)) 𝒂 ≡ (∣ ϕ ∣ ∘ (𝒔 i ̇ 𝑻)) 𝒂
  ΨH 𝒂 i = ap (λ - → - 𝒂) ((𝒕Ψ𝒔 i) 𝑨 SCloA)

  γ : ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻) (λ i → (𝒕 i ̇ 𝑻) 𝒂)) ≡ ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻) (λ i → (𝒔 i ̇ 𝑻) 𝒂))
  γ = ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻) (λ i → (𝒕 i ̇ 𝑻) 𝒂)) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
      (λ 𝒂 →   ∣ ϕ ∣((f ̂ 𝑻) (λ i → (𝒕 i ̇ 𝑻) 𝒂))) ≡⟨ gfe (λ 𝒂 → ∥ ϕ ∥ f (λ i → (𝒕 i ̇ 𝑻) 𝒂))  ⟩
      (λ 𝒂 → (f ̂ 𝑨) (λ i → ((∣ ϕ ∣ ∘ (𝒕 i ̇ 𝑻)) 𝒂))) ≡⟨ gfe (λ 𝒂 → ap (f ̂ 𝑨) (gfe λ i → ΨH 𝒂 i) ) ⟩
      (λ 𝒂 → (f ̂ 𝑨) (λ i → ((∣ ϕ ∣ ∘ (𝒔 i ̇ 𝑻)) 𝒂))) ≡⟨ (gfe (λ 𝒂 → ∥ ϕ ∥ f (λ i → (𝒔 i ̇ 𝑻) 𝒂)))⁻¹ ⟩
      (λ 𝒂 →   ∣ ϕ ∣((f ̂ 𝑻) (λ i → (𝒔 i ̇ 𝑻) 𝒂))) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
      ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻) (λ i → (𝒔 i ̇ 𝑻) 𝒂)) ∎

ΨSym : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →     symmetric (ΨRel{𝓠}{𝓧}{X}{𝒦})
ΨSym p q pΨRelq 𝑪 ϕ = (pΨRelq 𝑪 ϕ)⁻¹

ΨTra : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →     transitive (ΨRel{𝓠}{𝓧}{X}{𝒦})
ΨTra p q r pΨq qΨr 𝑪 ϕ = (pΨq 𝑪 ϕ) ∙ (qΨr 𝑪 ϕ)

ΨIsEquivalence : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →               IsEquivalence (ΨRel{𝓠}{𝓧}{X}{𝒦})
ΨIsEquivalence = record { rfl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁 ; sym = ΨSym ; trans = ΨTra }

ΨCon : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →     Congruence{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓧 = (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ⊔ 𝓧 ⁺)} (𝑻{𝓧}{X})
ΨCon {𝓠}{𝓧}{X}{𝒦} = mkcon (ΨRel{𝓠}{𝓧}{X}{𝒦}) Ψcompatible ΨIsEquivalence

-- The (relatively) free algebra
𝔽 : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →   Algebra (𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓠 ⁺ ⁺ ⊔ 𝓧 ⁺ ⁺) 𝑆
𝔽 {𝓠}{𝓧}{X}{𝒦} = 𝑻{𝓧}{X} ╱ (ΨCon{𝓠}{𝓧}{X}{𝒦})

-- Lemma 4.27. Let 𝒦 be a class of algebras, and ΨCon defined as above.
-- Then 𝔽 := 𝑻/ΨCon is isomorphic to an algebra in SP(𝒦).
-- Proof. 𝑻/ΨCon ↪ ⨅ 𝒜, where 𝒜 = {𝑨/θ : 𝑨/θ ∈ S(𝒦)}.
--        Therefore, 𝑻/ΨCon ≅ 𝑩, where 𝑩 is a subalgebra of ⨅ 𝒜 ∈ PS(𝒦).
--        This proves that 𝔽 is isomorphic to an algebra in SPS(𝒦) = SP(𝒦).

-- data SClo {𝓤 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)) : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
--   sbase : {𝑨 :  Algebra _ 𝑆} → 𝑨 ∈ 𝒦 → 𝑨 ∈ SClo 𝒦
--   sub : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ SClo 𝒦 → (sa : SubalgebrasOf 𝑨) → ∣ sa ∣ ∈ SClo 𝒦
AlgebrasInSClo𝒦 : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)} → Pred (Algebra 𝓠 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)
AlgebrasInSClo𝒦 {𝓠}{𝒦} = SClo{𝓤 = 𝓠} 𝒦

ΣSClo : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)} → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺ ̇
ΣSClo {𝓠}{𝒦} = Σ I ꞉ 𝓠 ̇ , Σ 𝒜 ꞉ (I → Algebra 𝓠 𝑆) , ((i : I) → 𝒜 i ∈ SClo{𝓤 = 𝓠} 𝒦)

⨅SClo : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →       ΣSClo{𝓠}{𝒦}
        ----------------
 →       Algebra 𝓠 𝑆

⨅SClo SS = ⨅ (fst ∥ SS ∥)


PS⊆SP : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →      PClo (SClo 𝒦) ⊆ SClo (PClo 𝒦)
PS⊆SP (pbase (sbase x)) = sbase (pbase x)
PS⊆SP {𝓠} {𝒦} (pbase (sub x sa)) = γ
 where
  ζ : ∣ sa ∣ ∈ SClo 𝒦
  ζ = sub x sa

  ξ : 𝒦 ⊆ PClo 𝒦
  ξ = pbase

  γ : SClo (PClo 𝒦) ∣ sa ∣
  γ = SClo-mono ξ (sub x sa)

PS⊆SP {𝓠} {𝒦} {.((∀ i → fst (_ i)) , (λ f proj i → snd (_ i) f (λ args → proj args i)))} (prod x) = {!!}


⨅Sclo∈SP : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
           (SS : ΣSClo{𝓠}{𝒦})
          -------------------------------
 →         (⨅SClo SS) ∈ (SClo (PClo 𝒦))

⨅Sclo∈SP {𝓠}{𝒦} SS = γ
 where
  I : 𝓠 ̇
  I = ∣ SS ∣
  𝒜 : I → Algebra 𝓠 𝑆
  𝒜 = fst ∥ SS ∥

  h₀ : ((i : I) → 𝒜 i ∈ SClo{𝓤 = 𝓠} 𝒦)
  h₀ = snd ∥ SS ∥

  h₁ : ((i : I) → 𝒜 i ∈ PClo (SClo 𝒦))
  h₁ i = pbase (h₀ i)

  P : Algebra 𝓠 𝑆
  P = ⨅SClo SS

  ζ : P ∈ PClo (SClo 𝒦)
  ζ = prod{I = I}{𝒜 = 𝒜} h₁

  γ : P ∈ SClo (PClo 𝒦)
  γ = PS⊆SP ζ


-- 𝔽embedding : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →            𝔽{𝓠}{𝓧}{X}{𝒦} ↪ ⨅ (SClo{𝓤 = 𝓠} 𝒦)
-- 𝔽embedding = ?
-- ∀ (𝑨 : Algebra 𝓠 𝑆) → (SCloA : 𝑨 ∈ SClo{𝓤 = 𝓠} 𝒦)
--               → ∣ 𝑻ϕ{𝓠}{𝓧}{X}{𝒦} (mkti 𝑨 SCloA) ∣ ∘ (p ̇ 𝑻) ≡ ∣ 𝑻ϕ (mkti 𝑨 SCloA) ∣ ∘ (q ̇ 𝑻)

𝔽∈SP𝒦 : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →       Σ I ꞉ _ ̇ , Σ 𝒜 ꞉ (I → Algebra _ 𝑆) , Σ sa ꞉ (SubalgebrasOf (⨅ 𝒜)) ,
           (∀ i → 𝒜 i ∈ 𝒦) × ((𝔽{𝓠}{𝓧}{X}{𝒦}) ≅ ∣ sa ∣)
𝔽∈SP𝒦 = {!!}




𝑻i⊧Ψ : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
       (𝑪 : Algebra 𝓠 𝑆)(SCloC : 𝑪 ∈ SClo{𝓤 = 𝓠} 𝒦)
       (p q : ∣ (𝑻{𝓧}{X}) ∣)  →  (p , q) ∈ Ψ{𝓠}{𝓧}{X}{𝒦}
      ----------------------------------------------------------------
 →     ∣ 𝑻ϕ(mkti 𝑪 SCloC) ∣ ∘ (p ̇ 𝑻) ≡ ∣ 𝑻ϕ(mkti 𝑪 SCloC) ∣ ∘ (q ̇ 𝑻)

𝑻i⊧Ψ 𝑪 SCloC p q pΨq = pCq
 where

  ϕ : hom 𝑻 𝑪
  ϕ = 𝑻ϕ(mkti 𝑪 SCloC)

  pCq : ∣ ϕ ∣ ∘ (p ̇ 𝑻) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻)
  pCq = pΨq 𝑪 SCloC


Ψ⊆ThSClo : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
 →         Ψ{𝓠}{𝓧}{X}{𝒦} ⊆ (Th (SClo{𝓤 = 𝓠} 𝒦))
Ψ⊆ThSClo {𝓠}{𝓧}{X}{𝒦} {p , q} pΨq {𝑪} SCloC = γ
 where
  ti : 𝑻img{𝓠 = 𝓠}
  ti = mkti {𝓠 = 𝓠} 𝑪 SCloC -- SClo→𝑻img

  ϕ : hom (𝑻{𝓧}{X}) 𝑪
  ϕ = 𝑻ϕ ti

  ϕE : Epic ∣ ϕ ∣
  ϕE = 𝑻ϕE ti

  ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
  ϕsur 𝒄 x = ϕE (𝒄 x)

  pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 ∣
  pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

  ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
  ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

  β : ∣ ϕ ∣ ∘ (p ̇ 𝑻) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻)
  β = pΨq 𝑪 SCloC

  γ : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
  γ = gfe λ 𝒄 →
   (p ̇ 𝑪) 𝒄                  ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
   (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ (comm-hom-term gfe 𝑻 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
   ∣ ϕ ∣ ((p ̇ 𝑻)(pre 𝒄))       ≡⟨ intensionality β (pre 𝒄) ⟩
   ∣ ϕ ∣ ((q ̇ 𝑻)(pre 𝒄))       ≡⟨ comm-hom-term gfe 𝑻 𝑪 ϕ q (pre 𝒄) ⟩
   (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
   (q ̇ 𝑪) 𝒄                   ∎

Ψ⊆Th𝒦 : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
         (p q : ∣ (𝑻{𝓧}{X}) ∣) → (p , q) ∈ Ψ → 𝒦 ⊧ p ≋ q
Ψ⊆Th𝒦 {𝓠}{𝓧}{X}{𝒦} p q pΨq {𝑨} KA = Ψ⊆ThSClo{𝒦 = 𝒦} {p , q} pΨq (sbase KA)


------------------
--Class Identities

--It follows from `vclo-id1` that, if 𝒦 is a class of structures, the set of identities
-- modeled by all structures in 𝒦 is the same as the set of identities modeled by all structures in VClo 𝒦.

-- Th (VClo 𝒦) is precisely the set of identities modeled by 𝒦
class-identities : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
                   (p q : ∣ 𝑻{𝓧}{X} ∣)
                  ----------------------------------------------------------
 →                 (_⊧_≋_ {𝓠}{𝓧}{X} 𝒦 p q)  ⇔  ((p , q) ∈ Th (VClo 𝒦))

class-identities {𝓠}{𝓧}{X}{𝒦} p q = (λ α VCloA → vclo-id1{𝓠}{𝓧}{X}{𝒦} p q α VCloA) ,
                                      (λ Thpq KA → Thpq (vbase KA))



-- Birkhoff's theorem: every variety is an equational class.
birkhoff : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
           (𝑨 : Algebra 𝓠 𝑆) → 𝑨 ∈ Mod{𝓠}{𝓧}{X} (Th{𝓠}{𝓧} (VClo{𝓠} 𝒦))
          --------------------------------------------
 →                     𝑨 ∈ VClo 𝒦

birkhoff {𝓠}{𝓧}{X}{𝒦} 𝑨 ModThVCloA = {!γ!}
 where
  F T : Algebra _ 𝑆
  F = 𝔽{𝓠}{𝓧}{X}{𝒦}
  T = 𝑻{𝓧}{X}

  h₀ : X → ∣ 𝑨 ∣
  h₀ = fst (𝕏 𝑨)

  h : hom T 𝑨
  h = lift-hom{𝑨 = 𝑨} h₀

  Ψ⊆ThVClo : Ψ{𝓠 = 𝓠}{𝒦 = 𝒦} ⊆ Th{𝓠}{𝓧} (VClo{𝓠} 𝒦)
  Ψ⊆ThVClo {p , q} pΨq =
   (lr-implication (class-identities p q)) (Ψ⊆Th𝒦{𝓠}{𝓧}{X}{𝒦} p q pΨq)

  Ψ⊆A⊧ : ∀{p}{q} → (p , q) ∈ Ψ → 𝑨 ⊧ p ≈ q
  Ψ⊆A⊧ {p} {q} pΨq = ModThVCloA p q (Ψ⊆ThVClo {p , q} pΨq)

  Ψ⊆Kerh : Ψ ⊆ KER-pred{B = ∣ 𝑨 ∣} ∣ h ∣
  Ψ⊆Kerh {p , q} pΨq = hp≡hq
   where
    hp≡hq : ∣ h ∣ p ≡ ∣ h ∣ q
    hp≡hq = hom-id-compatibility p q 𝑨 h (Ψ⊆A⊧{p}{q} pΨq)

  gg : Σ g ꞉ hom T F , Epic ∣ g ∣
  gg = (lift-hom{𝑨 = F} g₀) , {!!} -- (lift-of-epic-is-epic{𝓤 = (𝓞 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ⁺ ⁺)} g₀ g₀E)

   where
    g₀ : X → ∣ F ∣
    g₀ = fst (𝕏 F)

    g₀E : Epic g₀
    g₀E = snd (𝕏 F)

  g : hom T F
  g = fst gg

  gE : Epic ∣ g ∣
  gE = snd gg

  -- N.B. Ψ is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove 𝑨 is a homomorphic image of 𝔽(𝒦, 𝑻),
  -- it suffices to show that the kernel of the lift h : 𝑻 → 𝑨 contains Ψ.
  --
  --    𝑻---- g --->>𝑻/ψ    ψ = ker g ⊆ ker h => ∃ ϕ: T/ψ → A
  --    𝑻---- g --->>𝔽  (ker g = Ψ)
  --     \         .
  --      \       .
  --       h     ∃ϕ     (want: Ψ ⊆ ker h)
  --        \   .
  --         \ .
  --          V
  --          𝑨

  -----------------------------------
  kerg⊆kerh : KER-pred ∣ g ∣ ⊆ KER-pred ∣ h ∣
  kerg⊆kerh = {!!}

  -- ϕ' : Σ ϕ ꞉ (hom F 𝑨) , ∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ g ∣
  -- ϕ' = HomFactor gfe {T} {𝑨} {F} h g kerg⊆kerh gE

  --We need to find F : Algebra 𝒰 𝑆 such that F ∈ VClo and ∃ ϕ : hom F 𝑨 with ϕE : Epic ∣ ϕ ∣.
  --Then we can prove 𝑨 ∈ VClo 𝒦 by vhom F∈VClo (𝑨 , ∣ ϕ ∣ , (∥ ϕ ∥ , ϕE))
  -- since vhom : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ VClo 𝒦 → ((𝑩 , _ , _) : HomImagesOf 𝑨) → 𝑩 ∈ VClo 𝒦

  -- vcloF : F ∈ VClo 𝒦
  -- vcloF = {!!}

  ϕ : Σ h ꞉ (hom F 𝑨) , Epic ∣ h ∣
  ϕ = {!∣ ϕ' ∣ , ?!}

  hiF : HomImagesOf F
  hiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) )

  -- Finally, use 𝔽∈SP𝒦 to get an algebra 𝑩 ∈ VClo 𝒦 such that 𝔽 ≅ 𝑩.
  -- Then ∃ hom h : hom 𝑩 𝔽, so we can simply compose ϕ ∘ h : hom 𝑩 𝑨,
  -- which proves that 𝑨 ∈ VClo 𝒦, as desired.

  γ : 𝑨 ∈ VClo{𝓤 = 𝓠} 𝒦
  γ = {!!} -- vhom{𝓤 = 𝓠} {!!} {!!} -- vcloF hiF








































-- OLD STUFF
-- ⨅SClo' : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
-- {I : 𝓠 ̇}(𝒜 : I → Algebra 𝓠 𝑆) → ((i : I) → 𝒜 i ∈ SClo{𝓤 = 𝓠} 𝒦)
-- →        Algebra 𝓠 𝑆
-- ⨅SClo' 𝒜 h₀ = ⨅ 𝒜

-- ψ : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →  Pred (∣ 𝑻{𝓧}{X} ∣ × ∣ 𝑻{𝓧}{X} ∣) _
-- ψ {𝓠}{𝓧}{X}{𝒦} (p , q) = ∀ (𝑨 : Algebra 𝓠 𝑆) → (SCloA : 𝑨 ∈ SClo{𝓤 = 𝓠} 𝒦)
--                               → ∣ 𝑻ϕ (mkti 𝑨 SCloA) ∣ p ≡ ∣ 𝑻ϕ (mkti 𝑨 SCloA) ∣ q

-- ψRel : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →     Rel ∣ (𝑻{𝓧}{X}) ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)
-- ψRel {𝓠}{𝓧}{X}{𝒦} p q = ψ{𝓠}{𝓧}{X}{𝒦} (p , q)

-- ψcompatible : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →            compatible (𝑻{𝓧}{X}) (ψRel{𝓠}{𝓧}{X}{𝒦})
-- ψcompatible f {i} {j} iψj 𝑨 SCloA = γ
--  where
--   ti : 𝑻img
--   ti = mkti 𝑨 SCloA

--   ϕ : hom 𝑻 𝑨
--   ϕ = 𝑻ϕ ti

--   γ : ∣ ϕ ∣ ((f ̂ 𝑻) i) ≡ ∣ ϕ ∣ ((f ̂ 𝑻) j)
--   γ = ∣ ϕ ∣ ((f ̂ 𝑻) i) ≡⟨ ∥ ϕ ∥ f i ⟩
--       (f ̂ 𝑨) (∣ ϕ ∣ ∘ i) ≡⟨ ap (f ̂ 𝑨) (gfe λ x → ((iψj x) 𝑨 SCloA)) ⟩
--       (f ̂ 𝑨) (∣ ϕ ∣ ∘ j) ≡⟨ (∥ ϕ ∥ f j)⁻¹ ⟩
--       ∣ ϕ ∣ ((f ̂ 𝑻) j) ∎

-- ψSym : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →     symmetric (ψRel{𝓠}{𝓧}{X}{𝒦})
-- ψSym p q pψRelq 𝑪 ϕ = (pψRelq 𝑪 ϕ)⁻¹

-- ψTra : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →     transitive (ψRel{𝓠}{𝓧}{X}{𝒦})
-- ψTra p q r pψq qψr 𝑪 ϕ = (pψq 𝑪 ϕ) ∙ (qψr 𝑪 ϕ)

-- ψIsEquivalence : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →               IsEquivalence (ψRel{𝓠}{𝓧}{X}{𝒦})
-- ψIsEquivalence = record { rfl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁 ; sym = ψSym ; trans = ψTra }

-- ψCon : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →     Congruence{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓧} (𝑻{𝓧}{X})
-- ψCon {𝓠}{𝓧}{X}{𝒦} = mkcon (ψRel{𝓠}{𝓧}{X}{𝒦}) ψcompatible ψIsEquivalence

-- 𝔽 : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →   Algebra _ 𝑆
-- 𝔽 {𝓠}{𝓧}{X}{𝒦} = 𝑻{𝓧}{X} ╱ (ψCon{𝓠}{X}{𝒦})


--More tools for Birkhoff's theorem
--Here are some key facts/identities needed to complete the proof of Birkhoff's HSP theorem.

-- 𝑻i⊧ψ : {𝓠 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--        (𝑪 : Algebra 𝓠 𝑆)(SCloC : 𝑪 ∈ SClo{𝓤 = 𝓠} 𝒦)
--        (p q : ∣ (𝑻{𝓧}{X}) ∣)  →  (p , q) ∈ ψ
--       ----------------------------------------------------------------
--  →     ∣ 𝑻ϕ(mkti 𝑪 SCloC) ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ 𝑻ϕ(mkti 𝑪 SCloC) ∣ ((q ̇ 𝑻) ℊ)

-- 𝑻i⊧ψ 𝑪 SCloC p q pψq = γ
--  where

--   ϕ : hom 𝑻 𝑪
--   ϕ = 𝑻ϕ(mkti 𝑪 SCloC)

--   pCq : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
--   pCq = pψq 𝑪 SCloC

--   γ : ∣ ϕ ∣ ((p ̇ 𝑻) ℊ) ≡ ∣ ϕ ∣ ((q ̇ 𝑻) ℊ)
--   γ = (ap ∣ ϕ ∣(term-agree p))⁻¹ ∙ pCq ∙ (ap ∣ ϕ ∣(term-agree q))

-- PS⊆SP : {𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺)}
--  →      PClo (SClo 𝒦) ⊆ SClo (PClo 𝒦)
-- PS⊆SP {𝓠} {𝒦} {𝑨} (pbase {𝑨 = 𝑨} (sbase x)) = sbase (pbase x)
-- PS⊆SP {𝓠} {𝒦} {.(fst sa)} (pbase {𝑨 = .(fst sa)} (sub x sa)) = PS⊆SP{𝓠}{𝒦} (pbase (sub x sa))
-- PS⊆SP {𝓠} {𝒦} {.((∀ i → fst (_ i)) , (λ f proj i → snd (_ i) f (λ args → proj args i)))}
--  (prod{𝒜 = 𝒜} PCloSCloA) = γ
--   where
--    SCloPCloA : ∀ i → 𝒜 i ∈ SClo (PClo 𝒦)
--    SCloPCloA i = PS⊆SP (PCloSCloA i)

--    ⨅𝒜∈PS : ⨅ 𝒜 ∈ PClo (SClo 𝒦)
--    ⨅𝒜∈PS = prod PCloSCloA

--    γ : SClo (PClo 𝒦) (⨅ 𝒜)
--    γ = {!!}

