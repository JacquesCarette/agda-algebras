---
layout: default
title : Varieties.Preservation (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="Equation preservation">Equation preservation</a>

This section presents the [Varieties.Preservation][] module of the [Agda Universal Algebra Library][]. In this module we show that identities are preserved by closure operators H, S, and P.  This will establish the easy direction of Birkhoff's HSP Theorem.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Signatures using (Signature; 𝓞; 𝓥)
open import MGS-Subsingleton-Theorems using (global-dfunext)

module Varieties.Preservation {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext} where

open import Varieties.Varieties {𝑆 = 𝑆}{gfe} public

\end{code}



#### <a id="h-preserves-identities">H preserves identities</a>

First we prove that the closure operator H is compatible with identities that hold in the given class.

\begin{code}
module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 H-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → H{𝓤}{𝓤} 𝒦 ⊧ p ≋ q

 H-id1 p q α (hbase x) = ⊧-Lift-invar p q (α x)
 H-id1 p q α (hlift{𝑨} x) = ⊧-Lift-invar p q (H-id1 p q α x)

 H-id1 p q α (hhimg{𝑨}{𝑪} HA((𝑩 , ϕ , (ϕhom , ϕsur)), B≅C)) = ⊧-I-invar p q 𝑪 γ B≅C
  where
  β : 𝑨 ⊧ p ≈ q
  β = (H-id1 p q α) HA

  preim : ∀ 𝒃 x → ∣ 𝑨 ∣
  preim 𝒃 x = Inv ϕ (ϕsur (𝒃 x))

  ζ : ∀ 𝒃 → ϕ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = gfe λ x → InvIsInv ϕ (ϕsur (𝒃 x))

  γ : 𝑩 ⟦ p ⟧  ≡ 𝑩 ⟦ q ⟧
  γ = gfe λ 𝒃 → (𝑩 ⟦ p ⟧) 𝒃             ≡⟨ (ap (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹ ⟩
                (𝑩 ⟦ p ⟧)(ϕ ∘(preim 𝒃)) ≡⟨(comm-hom-term 𝑩(ϕ , ϕhom) p(preim 𝒃))⁻¹ ⟩
                ϕ((𝑨 ⟦ p ⟧)(preim 𝒃))   ≡⟨ ap ϕ (extfun β (preim 𝒃)) ⟩
                ϕ((𝑨 ⟦ q ⟧)(preim 𝒃))   ≡⟨ comm-hom-term 𝑩 (ϕ , ϕhom) q (preim 𝒃) ⟩
                (𝑩 ⟦ q ⟧)(ϕ ∘(preim 𝒃)) ≡⟨ ap (𝑩 ⟦ q ⟧) (ζ 𝒃) ⟩
                (𝑩 ⟦ q ⟧) 𝒃             ∎

 H-id1 p q α (hiso{𝑨}{𝑩} x x₁) = ⊧-I-invar p q 𝑩 (H-id1 p q α x) x₁

\end{code}

The converse of the foregoing result is almost too obvious to bother with. Nonetheless, we formalize it for completeness.

\begin{code}

 H-id2 : ∀ {𝓦} → (p q : Term X) → H{𝓤}{𝓦} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

 H-id2 p q Hpq KA = ⊧-lower-invar p q (Hpq (hbase KA))

\end{code}


#### <a id="s-preserves-identities">S preserves identities</a>

\begin{code}

 S-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → S{𝓤}{𝓤} 𝒦 ⊧ p ≋ q

 S-id1 p q α (sbase x) = ⊧-Lift-invar p q (α x)
 S-id1 p q α (slift x) = ⊧-Lift-invar p q ((S-id1 p q α) x)

 S-id1 p q α (ssub{𝑨}{𝑩} sA B≤A) =
  ⊧-S-class-invar p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
   where --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
   β : 𝑨 ⊧ p ≈ q
   β = S-id1 p q α sA

   Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Apq refl = β

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Apq y

 S-id1 p q α (ssubw{𝑨}{𝑩} sA B≤A) =
  ⊧-S-class-invar p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
   where  --Apply S-⊧ to the class 𝒦 ∪ ｛ 𝑨 ｝
   β : 𝑨 ⊧ p ≈ q
   β = S-id1 p q α sA

   Apq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Apq refl = β

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Apq y

 S-id1 p q α (siso{𝑨}{𝑩} x x₁) = ⊧-I-invar p q 𝑩 (S-id1 p q α x) x₁

\end{code}

Again, the obvious converse is barely worth the bits needed to formalize it.

\begin{code}

 S-id2 : ∀{𝓦}(p q : Term X) → S{𝓤}{𝓦}𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

 S-id2 p q Spq {𝑨} KA = ⊧-lower-invar p q (Spq (sbase KA))

\end{code}


#### <a id="p-preserves-identities">P preserves identities</a>

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 P-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → P{𝓤}{𝓤} 𝒦 ⊧ p ≋ q

 P-id1 p q α (pbase x) = ⊧-Lift-invar p q (α x)
 P-id1 p q α (pliftu x) = ⊧-Lift-invar p q ((P-id1 p q α) x)
 P-id1 p q α (pliftw x) = ⊧-Lift-invar p q ((P-id1 p q α) x)

 P-id1 p q α (produ{I}{𝒜} x) = ⊧-P-lift-invar I 𝒜 p q IH
  where
  IH : ∀ i → (Lift-alg (𝒜 i) 𝓤) ⟦ p ⟧ ≡ (Lift-alg (𝒜 i) 𝓤) ⟦ q ⟧
  IH i = ⊧-Lift-invar p q ((P-id1 p q α) (x i))

 P-id1 p q α (prodw{I}{𝒜} x) = ⊧-P-lift-invar I 𝒜 p q IH
  where
  IH : ∀ i → Lift-alg (𝒜 i) 𝓤 ⟦ p ⟧ ≡ Lift-alg (𝒜 i) 𝓤 ⟦ q ⟧
  IH i = ⊧-Lift-invar p q ((P-id1 p q α) (x i))

 P-id1 p q α (pisou{𝑨}{𝑩} x x₁) = ⊧-I-invar p q 𝑩 (P-id1 p q α x) x₁
 P-id1 p q α (pisow{𝑨}{𝑩} x x₁) = ⊧-I-invar p q 𝑩 (P-id1 p q α x) x₁

\end{code}

...and conversely...

\begin{code}

 P-id2 : ∀ {𝓦}(p q : Term X) → P{𝓤}{𝓦} 𝒦 ⊧ p ≋ q → 𝒦 ⊧ p ≋ q

 P-id2 p q PKpq KA = ⊧-lower-invar p q (PKpq (pbase KA))

\end{code}


#### <a id="v-preserves-identities">V preserves identities</a>

Finally, we prove the analogous preservation lemmas for the closure operator `V`.

\begin{code}

 V-id1 : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{𝓤}{𝓤} 𝒦 ⊧ p ≋ q

 V-id1 p q α (vbase x) = ⊧-Lift-invar p q (α x)
 V-id1 p q α (vlift{𝑨} x) = ⊧-Lift-invar p q ((V-id1 p q α) x)
 V-id1 p q α (vliftw{𝑨} x) = ⊧-Lift-invar p q ((V-id1 p q α) x)

 V-id1 p q α (vhimg{𝑨}{𝑪}VA((𝑩 , ϕ , (ϕh , ϕE)) , B≅C)) = ⊧-I-invar p q 𝑪 γ B≅C
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1 p q α VA

  preim : ∀ 𝒃 x → ∣ 𝑨 ∣
  preim 𝒃 x = (Inv ϕ (ϕE (𝒃 x)))

  ζ : ∀ 𝒃 → ϕ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = gfe λ x → InvIsInv ϕ (ϕE (𝒃 x))

  γ : (𝑩 ⟦ p ⟧) ≡ (𝑩 ⟦ q ⟧)
  γ = gfe λ 𝒃 → (𝑩 ⟦ p ⟧) 𝒃             ≡⟨ (ap (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹ ⟩
                (𝑩 ⟦ p ⟧)(ϕ ∘(preim 𝒃)) ≡⟨(comm-hom-term 𝑩(ϕ , ϕh) p(preim 𝒃))⁻¹ ⟩
                ϕ ((𝑨 ⟦ p ⟧)(preim 𝒃))  ≡⟨ ap ϕ (extfun IH (preim 𝒃)) ⟩
                ϕ ((𝑨 ⟦ q ⟧)(preim 𝒃))  ≡⟨ comm-hom-term 𝑩 (ϕ , ϕh) q (preim 𝒃) ⟩
                (𝑩 ⟦ q ⟧)(ϕ ∘(preim 𝒃)) ≡⟨ ap (𝑩 ⟦ q ⟧) (ζ 𝒃) ⟩
                (𝑩 ⟦ q ⟧) 𝒃             ∎

 V-id1 p q α (vssub {𝑨}{𝑩} VA B≤A) =
  ⊧-S-class-invar p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 p q α VA

   Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Asinglepq refl = IH

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Asinglepq y

 V-id1 p q α ( vssubw {𝑨}{𝑩} VA B≤A ) =
  ⊧-S-class-invar p q γ (𝑩 , 𝑨 , (𝑩 , B≤A) , inj₂ refl , ≅-refl)
   where
   IH : 𝑨 ⊧ p ≈ q
   IH = V-id1 p q α VA

   Asinglepq : ｛ 𝑨 ｝ ⊧ p ≋ q
   Asinglepq refl = IH

   γ : (𝒦 ∪ ｛ 𝑨 ｝) ⊧ p ≋ q
   γ {𝑩} (inj₁ x) = α x
   γ {𝑩} (inj₂ y) = Asinglepq y

 V-id1 p q α (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 p q λ i → V-id1 p q α (V𝒜 i)
 V-id1 p q α (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 p q λ i → V-id1 p q α (V𝒜 i)
 V-id1 p q α (visou{𝑨}{𝑩} VA A≅B) = ⊧-I-invar p q 𝑩 (V-id1 p q α VA) A≅B
 V-id1 p q α (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar p q 𝑩 (V-id1 p q α VA) A≅B

\end{code}

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 V-id1' : (p q : Term X) → 𝒦 ⊧ p ≋ q → V{𝓤}{ov 𝓤 ⁺} 𝒦 ⊧ p ≋ q

 V-id1' p q α (vbase x) = ⊧-Lift-invar p q (α x)
 V-id1' p q α (vlift{𝑨} x) = ⊧-Lift-invar p q ((V-id1 p q α) x)
 V-id1' p q α (vliftw{𝑨} x) = ⊧-Lift-invar p q ((V-id1' p q α) x)

 V-id1' p q α (vhimg{𝑨}{𝑪} VA ((𝑩 , ϕ , (ϕh , ϕE)) , B≅C)) = ⊧-I-invar p q 𝑪 γ B≅C
  where
  IH : 𝑨 ⊧ p ≈ q
  IH = V-id1' p q α VA

  preim : ∀ 𝒃 x → ∣ 𝑨 ∣
  preim 𝒃 x = (Inv ϕ (ϕE (𝒃 x)))

  ζ : ∀ 𝒃 → ϕ ∘ (preim 𝒃) ≡ 𝒃
  ζ 𝒃 = gfe λ x → InvIsInv ϕ (ϕE (𝒃 x))

  γ : 𝑩 ⟦ p ⟧ ≡ 𝑩 ⟦ q ⟧
  γ = gfe λ 𝒃 → (𝑩 ⟦ p ⟧) 𝒃               ≡⟨(ap (𝑩 ⟦ p ⟧) (ζ 𝒃))⁻¹ ⟩
                (𝑩 ⟦ p ⟧) (ϕ ∘ (preim 𝒃)) ≡⟨(comm-hom-term 𝑩 (ϕ , ϕh) p (preim 𝒃))⁻¹ ⟩
                ϕ((𝑨 ⟦ p ⟧)(preim 𝒃))     ≡⟨ ap ϕ (extfun IH (preim 𝒃))⟩
                ϕ((𝑨 ⟦ q ⟧)(preim 𝒃))     ≡⟨ comm-hom-term 𝑩 (ϕ , ϕh) q (preim 𝒃)⟩
                (𝑩 ⟦ q ⟧)(ϕ ∘ (preim 𝒃))   ≡⟨ ap (𝑩 ⟦ q ⟧) (ζ 𝒃)⟩
                (𝑩 ⟦ q ⟧) 𝒃                ∎

 V-id1' p q α (vssub{𝑨}{𝑩} VA B≤A) = ⊧-S-invar p q 𝑩 (V-id1 p q α VA) B≤A
 V-id1' p q α (vssubw {𝑨}{𝑩} VA B≤A) = ⊧-S-invar p q 𝑩 (V-id1' p q α VA) B≤A
 V-id1' p q α (vprodu{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 p q λ i → V-id1 p q α (V𝒜 i)
 V-id1' p q α (vprodw{I}{𝒜} V𝒜) = ⊧-P-invar I 𝒜 p q λ i → V-id1' p q α (V𝒜 i)
 V-id1' p q α (visou {𝑨}{𝑩} VA A≅B) = ⊧-I-invar p q 𝑩 (V-id1 p q α VA) A≅B
 V-id1' p q α (visow{𝑨}{𝑩} VA A≅B) = ⊧-I-invar p q 𝑩 (V-id1' p q α VA) A≅B

\end{code}

Once again, and for the last time, completeness dictates that we formalize the coverse, however obvious it may be.

\begin{code}

 V-id2 : ∀ {𝓦}(p q : Term X) → (V{𝓤}{𝓦} 𝒦 ⊧ p ≋ q) → (𝒦 ⊧ p ≋ q)
 V-id2 p q Vpq {𝑨} KA = ⊧-lower-invar p q (Vpq (vbase KA))

\end{code}

#### <a id="class-identities">Class identities</a>

From `V-id1` it follows that if 𝒦 is a class of structures, then the set of identities modeled by all structures in `𝒦` is equivalent to the set of identities modeled by all structures in `V 𝒦`.  In other terms, `Th (V 𝒦)` is precisely the set of identities modeled by `𝒦`.   We formalize this observation as follows.

\begin{code}

module _ {𝓤 𝓧 : Universe}{X : 𝓧 ̇} {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 𝒱 : Pred (Algebra (ov 𝓤 ⁺) 𝑆) (ov 𝓤 ⁺ ⁺)
 𝒱 = V{𝓤}{ov 𝓤 ⁺} 𝒦

 class-ids-⇒ : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊧ p ≋ q  →  (p , q) ∈ Th 𝒱

 class-ids-⇒ p q pKq VCloA = V-id1' p q pKq VCloA


 class-ids-⇐ : (p q : ∣ 𝑻 X ∣) → (p , q) ∈ Th 𝒱 →  𝒦 ⊧ p ≋ q

 class-ids-⇐ p q Thpq {𝑨} KA = ⊧-lower-invar p q (Thpq (vbase KA))


 class-identities : (p q : ∣ 𝑻 X ∣) → 𝒦 ⊧ p ≋ q  ⇔  ((p , q) ∈ Th 𝒱)

 class-identities p q = class-ids-⇒ p q , class-ids-⇐ p q

\end{code}

----------------------------

[← Varieties.Varieties](Varieties.Varieties.html)
<span style="float:right;">[FreeAlgebras →](Varieties.FreeAlgebras.html)</span>

{% include UALib.Links.md %}

