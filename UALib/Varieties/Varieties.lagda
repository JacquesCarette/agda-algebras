---
layout: default
title : UALib.Varieties.Varieties module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="inductive-types-h-s-p-and-v">Inductive Types H, S, P, and V</a>

This section presents the [UALib.Varieties.Varieties][] module of the [Agda Universal Algebra Library][].

Fix a signature 𝑆, let 𝒦 be a class of 𝑆-algebras, and define

* H 𝒦 = algebras isomorphic to a homomorphic image of a members of 𝒦;
* S 𝒦 = algebras isomorphic to a subalgebra of a member of 𝒦;
* P 𝒦 = algebras isomorphic to a product of members of 𝒦.

A straight-forward verification confirms that H, S, and P are **closure operators** (expansive, monotone, and idempotent).  A class 𝒦 of 𝑆-algebras is said to be *closed under the taking of homomorphic images* provided `H 𝒦 ⊆ 𝒦`. Similarly, 𝒦 is *closed under the taking of subalgebras* (resp., *arbitrary products*) provided `S 𝒦 ⊆ 𝒦` (resp., `P 𝒦 ⊆ 𝒦`). The operators H, S, and P can be composed with one another repeatedly, forming yet more closure operators.

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class `H 𝒦` (resp., `S 𝒦`; resp., `P 𝒦`) is closed under isomorphism.

A **variety** is a class of algebras, in the same signature, that is closed under the taking of homomorphic images, subalgebras, and arbitrary products.  To represent varieties we define inductive types for the closure operators `H`, `S`, and `P` that are composable.  Separately, we define an inductive type `V` which simultaneously represents closure under all three operators, `H`, `S`, and `P`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Varieties.Varieties
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import UALib.Varieties.EquationalLogic{𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

-----------------------------------

#### <a id="homomorphic-closure">Homomorphism closure</a>

We define the inductive type `H` to represent classes of algebras that include all homomorphic images of algebras in the class; i.e., classes that are closed under the taking of homomorphic images.

\begin{code}

--Closure wrt H
data H {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(ov(𝓤 ⊔ 𝓦)) where
  hbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ H 𝒦
  hlift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ H 𝒦
  hhimg : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓦} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ H 𝒦
  hiso  : {𝑨 : Algebra _ 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ H{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ H 𝒦

\end{code}

<!-- We say that a class 𝒦 is **closed under** `H` (or `H`-**closed**) provided `H 𝒦 ⊆ 𝒦`. -->

--------------------------------

#### <a id="subalgebra-closure">Subalgebra closure</a>

The most useful inductive type that we have found for representing classes of algebras that are closed under the taking of subalgebras as an inductive type.

\begin{code}

--Closure wrt S
data S {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆) (ov 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆) (ov(𝓤 ⊔ 𝓦)) where
  sbase : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ S 𝒦
  slift : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ S 𝒦
  ssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
  ssubw : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓦} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦
  siso  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ S 𝒦

\end{code}

<!-- A class 𝒦 is **closed under** `S` (or `S`-**closed**) provided `S 𝒦 ⊆ 𝒦` -->

-----------------------------------------

#### <a id="product-closure">Product closure</a>

The most useful inductive type that we have found for representing classes of algebras closed under arbitrary products is the following.

\begin{code}

data P {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) : Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(ov(𝓤 ⊔ 𝓦)) where
  pbase  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ P 𝒦
  pliftu : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ P 𝒦
  pliftw : {𝑨 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ P 𝒦
  produ  : {I : 𝓦 ̇ }{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
  prodw  : {I : 𝓦 ̇ }{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ P{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ P 𝒦
  pisou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦
  pisow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ P{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ P 𝒦

\end{code}

<!-- A class 𝒦 is **closed under** `P` (or `P`-**closed**) provided `P 𝒦 ⊆ 𝒦`. -->

-----------------------------------------------

#### <a id="variety-closure">Varietal closure</a>

A class 𝒦 of 𝑆-algebras is called a **variety** if it is closed under each of the closure operators H, S, and P introduced above; the corresponding closure operator is often denoted 𝕍, but we will typically denote it by `V`.

Thus, if 𝒦 is a class of 𝑆-algebras, then the **variety generated by** 𝒦 is denoted by `V 𝒦` and defined to be the smallest class that contains 𝒦 and is closed under `H`, `S`, and `P`.

We now define `V` as an inductive type.

\begin{code}

data V {𝓤 𝓦 : Universe}(𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) :
 Pred (Algebra (𝓤 ⊔ 𝓦) 𝑆)(ov(𝓤 ⊔ 𝓦)) where
  vbase  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ 𝒦 → lift-alg 𝑨 𝓦 ∈ V 𝒦
  vlift  : {𝑨 : Algebra 𝓤 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → lift-alg 𝑨 𝓦 ∈ V 𝒦
  vliftw : {𝑨 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → lift-alg 𝑨 (𝓤 ⊔ 𝓦) ∈ V 𝒦
  vhimg  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑩 is-hom-image-of 𝑨 → 𝑩 ∈ V 𝒦
  vssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V 𝒦
  vssubw : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ V 𝒦
  vprodu : {I : 𝓦 ̇}{𝒜 : I → Algebra 𝓤 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓤} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
  vprodw : {I : 𝓦 ̇}{𝒜 : I → Algebra _ 𝑆} → (∀ i → (𝒜 i) ∈ V{𝓤}{𝓦} 𝒦) → ⨅ 𝒜 ∈ V 𝒦
  visou  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓤} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦
  visow  : {𝑨 𝑩 : Algebra _ 𝑆} → 𝑨 ∈ V{𝓤}{𝓦} 𝒦 → 𝑨 ≅ 𝑩 → 𝑩 ∈ V 𝒦

\end{code}

With the closure operator V representing closure under HSP, we formally represent what it means to be a variety of algebras as follows.

\begin{code}

is-variety : {𝓤 : Universe}(𝒱 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)) → ov 𝓤 ̇
is-variety{𝓤} 𝒱 = V{𝓤}{𝓤} 𝒱 ⊆ 𝒱

variety : (𝓤 : Universe) → (ov 𝓤)⁺ ̇
variety 𝓤 = Σ 𝒱 ꞉ (Pred (Algebra 𝓤 𝑆)(ov 𝓤)) , is-variety 𝒱

\end{code}



-------------------------------

#### <a id="closure-properties">Closure properties</a>

The types defined above represent operators with useful closure properties. We now prove a handful of such properties since we will need them later.

\begin{code}

-- P is a closure operator; in particular, it's expansive.
P-expa : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → 𝒦 ⊆ P{𝓤}{𝓤} 𝒦
P-expa{𝓤}{𝒦} {𝑨} KA = pisou{𝑨 = (lift-alg 𝑨 𝓤)}{𝑩 = 𝑨} (pbase KA) (sym-≅ lift-alg-≅)

-- P is a closure operator; in particular, it's idempotent.
P-idemp : {𝓤 : Universe}{𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →        P{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓤 ⊔ 𝓦} 𝒦) ⊆ P{𝓤}{𝓤 ⊔ 𝓦} 𝒦

P-idemp (pbase x) = pliftw x
P-idemp {𝓤}{𝓦} (pliftu x) = pliftw (P-idemp{𝓤}{𝓦} x)
P-idemp {𝓤}{𝓦} (pliftw x) = pliftw (P-idemp{𝓤}{𝓦} x)
P-idemp {𝓤}{𝓦} (produ x) = prodw (λ i → P-idemp{𝓤}{𝓦} (x i))
P-idemp {𝓤}{𝓦} (prodw x) = prodw (λ i → P-idemp{𝓤}{𝓦} (x i))
P-idemp {𝓤}{𝓦} (pisou x x₁) = pisow (P-idemp{𝓤}{𝓦} x) x₁
P-idemp {𝓤}{𝓦} (pisow x x₁) = pisow (P-idemp{𝓤}{𝓦} x) x₁

-- S is a closure operator; in particular, it's monotone.
S-mono : {𝓤 𝓦 : Universe}{𝒦 𝒦' : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →       𝒦 ⊆ 𝒦'  →  S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤}{𝓦} 𝒦'
S-mono ante (sbase x) = sbase (ante x)
S-mono {𝓤}{𝓦}{𝒦}{𝒦'} ante (slift{𝑨} x) = slift{𝓤}{𝓦}{𝒦'} (S-mono{𝓤}{𝓤} ante x)
S-mono ante (ssub{𝑨}{𝑩} sA B≤A) = ssub (S-mono ante sA) B≤A
S-mono ante (ssubw{𝑨}{𝑩} sA B≤A) = ssubw (S-mono ante sA) B≤A
S-mono ante (siso x x₁) = siso (S-mono ante x) x₁

\end{code}

We sometimes want to go back and forth between our two representations of subalgebras of algebras in a class. The tools `subalgebra→S` and `S→subalgebra` are made for that purpose.

\begin{code}

subalgebra→S : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
               {𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆} → 𝑪 IsSubalgebraOfClass 𝒦
               ---------------------------------------------------
 →                           𝑪 ∈ S{𝓤}{𝓦} 𝒦

subalgebra→S {𝓤}{𝓦}{𝒦}{𝑪} (𝑨 , ((𝑩 , B≤A) , KA , C≅B)) = ssub sA C≤A
 where
  C≤A : 𝑪 ≤ 𝑨
  C≤A = Iso-≤ 𝑨 𝑪 B≤A C≅B

  slAu : lift-alg 𝑨 𝓤 ∈ S{𝓤}{𝓤} 𝒦
  slAu = sbase KA

  sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦
  sA = siso slAu (sym-≅ lift-alg-≅)


module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

 S→subalgebra : {𝑩 : Algebra 𝓤 𝑆} → 𝑩 ∈ S{𝓤}{𝓤} 𝒦  →  𝑩 IsSubalgebraOfClass 𝒦
 S→subalgebra (sbase{𝑩} x) = 𝑩 , (𝑩 , refl-≤) , x , (sym-≅ lift-alg-≅)
 S→subalgebra (slift{𝑩} x) = ∣ BS ∣ , SA , KA , TRANS-≅ (sym-≅ lift-alg-≅) B≅SA
  where
   BS : 𝑩 IsSubalgebraOfClass 𝒦
   BS = S→subalgebra x

   SA : Subalgebra ∣ BS ∣
   SA = fst ∥ BS ∥

   KA : ∣ BS ∣ ∈ 𝒦
   KA = ∣ snd ∥ BS ∥ ∣

   B≅SA : 𝑩 ≅ ∣ SA ∣
   B≅SA = ∥ snd ∥ BS ∥ ∥

 S→subalgebra {𝑩} (ssub{𝑨} sA B≤A) = γ
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = transitivity-≤ 𝑩{∣ SA ∣}{∣ AS ∣} B≤SA ∥ SA ∥
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ =  ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , refl-≅

 S→subalgebra {𝑩} (ssubw{𝑨} sA B≤A) = γ
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   B≤SA : 𝑩 ≤ ∣ SA ∣
   B≤SA = TRANS-≤-≅ 𝑩 ∣ SA ∣ B≤A (∥ snd ∥ AS ∥ ∥)
   B≤AS : 𝑩 ≤ ∣ AS ∣
   B≤AS = transitivity-≤ 𝑩{∣ SA ∣}{∣ AS ∣} B≤SA ∥ SA ∥
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ =  ∣ AS ∣ , (𝑩 , B≤AS) , ∣ snd ∥ AS ∥ ∣ , refl-≅

 S→subalgebra {𝑩} (siso{𝑨} sA A≅B) = γ
  where
   AS : 𝑨 IsSubalgebraOfClass 𝒦
   AS = S→subalgebra sA
   SA : Subalgebra ∣ AS ∣
   SA = fst ∥ AS ∥
   A≅SA : 𝑨 ≅ ∣ SA ∣
   A≅SA = snd ∥ snd AS ∥
   γ : 𝑩 IsSubalgebraOfClass 𝒦
   γ = ∣ AS ∣ , SA ,  ∣ snd ∥ AS ∥ ∣ , (TRANS-≅ (sym-≅ A≅B) A≅SA)

\end{code}

Next we observe that lifting to a higher universe does not break the property of being a subalgebra of an algebra of a class.  In other words, if we lift a subalgebra of an algebra in a class, the result is still a subalgebra of an algebra in the class.

\begin{code}

lift-alg-subP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}{𝑩 : Algebra 𝓤 𝑆}

 →                𝑩 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
            ---------------------------------------------------
 →           (lift-alg 𝑩 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lift-alg-subP {𝓤} {𝓦} {𝒦} {𝑩} (𝑨 , (𝑪 , C≤A) , pA , B≅C ) = γ
 where
  lA lB lC : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦
  lB = lift-alg 𝑩 𝓦
  lC = lift-alg 𝑪 𝓦

  lC≤lA : lC ≤ lA
  lC≤lA = lift-alg-≤ 𝑪 {𝑨} C≤A
  plA : lA ∈ P{𝓤}{𝓦} 𝒦
  plA = pliftu pA

  γ : lB IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  γ = lA , (lC , lC≤lA) , plA , (lift-alg-iso 𝓤 𝓦 𝑩 𝑪 B≅C)

\end{code}

The next lemma would be too obvoius to care about were it not for the fact that we'll need it later, so it too must be formalized.

\begin{code}

S⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →     S{𝓤}{𝓦} 𝒦 ⊆ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)

S⊆SP {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (sbase{𝑨} x) =
 siso spllA (sym-≅ lift-alg-≅)
  where
   llA : Algebra (𝓤 ⊔ 𝓦) 𝑆
   llA = lift-alg (lift-alg 𝑨 𝓦) (𝓤 ⊔ 𝓦)

   spllA : llA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
   spllA = sbase{𝓤 = (𝓤 ⊔ 𝓦)}{𝓦 = (𝓤 ⊔ 𝓦)} (pbase x)

S⊆SP {𝓤} {𝓦} {𝒦} {.(lift-alg 𝑨 𝓦)} (slift{𝑨} x) =
 subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lift-alg 𝑨 𝓦} lAsc
  where
   splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
   splAu = S⊆SP{𝓤}{𝓤} x

   Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
   Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

   lAsc : (lift-alg 𝑨 𝓦) IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
   lAsc = lift-alg-subP Asc

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (ssub{𝑨} sA B≤A) =
 ssub{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp (lift-alg-sub-lift 𝑨 B≤A)
  where
   lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
   lA = lift-alg 𝑨 𝓦

   splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
   splAu = S⊆SP{𝓤}{𝓤} sA

   Asc : 𝑨 IsSubalgebraOfClass (P{𝓤}{𝓤} 𝒦)
   Asc = S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu

   lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
   lAsc = lift-alg-subP Asc

   lAsp : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
   lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (ssubw{𝑨} sA B≤A) = γ
 where
  spA : 𝑨 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  spA = S⊆SP sA
  γ : 𝑩 ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  γ = ssubw{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} spA B≤A

S⊆SP {𝓤} {𝓦} {𝒦} {𝑩} (siso{𝑨} sA A≅B) = siso{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} lAsp lA≅B
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  splAu : 𝑨 ∈ S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
  splAu = S⊆SP{𝓤}{𝓤} sA

  lAsc : lA IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)
  lAsc = lift-alg-subP (S→subalgebra{𝓤}{P{𝓤}{𝓤} 𝒦}{𝑨} splAu)

  lAsp : lA ∈ S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦)
  lAsp = subalgebra→S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦}{P{𝓤}{𝓦} 𝒦}{lA} lAsc

  lA≅B : lA ≅ 𝑩
  lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B

\end{code}

We need to formalize one more lemma before arriving the short term objective of this section, which is the proof of the inclusion PS⊆SP.

\begin{code}

lemPS⊆SP : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}{hfe : hfunext 𝓦 𝓤}
 →         {I : 𝓦 ̇}{ℬ : I → Algebra 𝓤 𝑆}
 →         (∀ i → (ℬ i) IsSubalgebraOfClass 𝒦)
           -------------------------------------
 →         ⨅ ℬ IsSubalgebraOfClass (P{𝓤}{𝓦} 𝒦)

lemPS⊆SP {𝓤}{𝓦}{𝒦}{hfe}{I}{ℬ} B≤K = ⨅ 𝒜 , (⨅ SA , ⨅SA≤⨅𝒜 ) , ξ , γ
 where
  𝒜 : I → Algebra 𝓤 𝑆
  𝒜 = λ i → ∣ B≤K i ∣

  SA : I → Algebra 𝓤 𝑆
  SA = λ i → ∣ fst ∥ B≤K i ∥ ∣

  KA : ∀ i → 𝒜 i ∈ 𝒦
  KA = λ i → ∣ snd ∥ B≤K i ∥ ∣

  B≅SA : ∀ i → ℬ i ≅ SA i
  B≅SA = λ i → ∥ snd ∥ B≤K i ∥ ∥

  pA : ∀ i → lift-alg (𝒜 i) 𝓦 ∈ P{𝓤}{𝓦} 𝒦
  pA = λ i → pbase (KA i)

  SA≤𝒜 : ∀ i → (SA i) IsSubalgebraOf (𝒜 i)
  SA≤𝒜 = λ i → snd ∣ ∥ B≤K i ∥ ∣

  h : ∀ i → ∣ SA i ∣ → ∣ 𝒜 i ∣
  h = λ i → ∣ SA≤𝒜 i ∣

  ⨅SA≤⨅𝒜 : ⨅ SA ≤ ⨅ 𝒜
  ⨅SA≤⨅𝒜 = i , ii , iii
   where
    i : ∣ ⨅ SA ∣ → ∣ ⨅ 𝒜 ∣
    i = λ x i → (h i) (x i)
    ii : is-embedding i
    ii = embedding-lift{𝓠 = 𝓤}{𝓤 = 𝓤}{𝓘 = 𝓦} hfe hfe {I}{SA}{𝒜}h(λ i → fst ∥ SA≤𝒜 i ∥)
    iii : is-homomorphism (⨅ SA) (⨅ 𝒜) i
    iii = λ 𝑓 𝒂 → gfe λ i → (snd ∥ SA≤𝒜 i ∥) 𝑓 (λ x → 𝒂 x i)

  ξ : ⨅ 𝒜 ∈ P 𝒦
  ξ = produ{𝓤}{𝓦}{I = I}{𝒜 = 𝒜} (λ i → P-expa (KA i))

  γ : ⨅ ℬ ≅ ⨅ SA
  γ = ⨅≅ gfe B≅SA

\end{code}

#### PS(𝒦) ⊆ SP(𝒦)

Finally, we are in a position to prove that a product of subalgebras of algebras in a class 𝒦 is a subalgebra of a product of algebras in 𝒦.

\begin{code}

module _ {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} {hfe : hfunext (ov 𝓤)(ov 𝓤)} where

 ov𝓾 : Universe
 ov𝓾 = ov 𝓤

 PS⊆SP : (P{ov𝓾}{ov𝓾} (S{𝓤}{ov𝓾} 𝒦)) ⊆ (S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))
 PS⊆SP (pbase (sbase x)) = sbase (pbase x)
 PS⊆SP (pbase (slift{𝑨} x)) = slift (S⊆SP{𝓤}{ov𝓾}{𝒦} (slift x))
 PS⊆SP (pbase {𝑩} (ssub{𝑨} sA B≤A)) =
  siso (ssub{𝓤 = ov𝓾} (S⊆SP{𝓤}{ov𝓾}{𝒦} (slift sA)) (lift-alg-≤ 𝑩{𝑨} B≤A)) refl-≅
 PS⊆SP (pbase {𝑩}(ssubw{𝑨} sA B≤A)) =
  ssub{𝓤 = ov𝓾}(slift{ov𝓾}{ov𝓾}(S⊆SP sA))(lift-alg-≤ 𝑩{𝑨} B≤A)
 PS⊆SP (pbase (siso{𝑨}{𝑩} x A≅B)) = siso (S⊆SP (slift x)) (lift-alg-iso 𝓤 ov𝓾 𝑨 𝑩 A≅B)
 PS⊆SP (pliftu x) = slift (PS⊆SP x)
 PS⊆SP (pliftw x) = slift (PS⊆SP x)

 PS⊆SP (produ{I}{𝒜} x) = γ
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov𝓾} 𝒦)
   ξ i = S→subalgebra{𝒦 = (P 𝒦)} (PS⊆SP (x i))

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))
   η' = lemPS⊆SP{𝓤 = ov𝓾}{ov𝓾}{𝒦 = (P 𝒦)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))
   η = subalgebra→S{𝓤 = (ov𝓾)}{𝓦 = ov𝓾}{𝒦 = (P (P 𝒦))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦)
   γ = (S-mono{𝓤 = ov𝓾}{𝒦 = (P (P 𝒦))}{𝒦' = (P 𝒦)} (P-idemp)) η

 PS⊆SP (prodw{I}{𝒜} x) = γ
  where
   ξ : (i : I) → (𝒜 i) IsSubalgebraOfClass (P{𝓤}{ov𝓾} 𝒦)
   ξ i = S→subalgebra{𝒦 = (P 𝒦)} (PS⊆SP (x i))

   η' : ⨅ 𝒜 IsSubalgebraOfClass (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))
   η' = lemPS⊆SP{𝓤 = ov𝓾}{ov𝓾}{𝒦 = (P 𝒦)}{hfe}{I = I}{ℬ = 𝒜} ξ

   η : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦))
   η = subalgebra→S{𝓤 = (ov𝓾)}{𝓦 = ov𝓾}{𝒦 = (P (P 𝒦))}{𝑪 = ⨅ 𝒜} η'

   γ : ⨅ 𝒜 ∈ S{ov𝓾}{ov𝓾} (P{𝓤}{ov𝓾} 𝒦)
   γ = (S-mono{𝓤 = ov𝓾}{𝒦 = (P (P 𝒦))}{𝒦' = (P 𝒦)} (P-idemp)) η

 PS⊆SP (pisou{𝑨}{𝑩} pA A≅B) = siso{ov𝓾}{ov𝓾}{P{𝓤}{ov𝓾} 𝒦}{𝑨}{𝑩} (PS⊆SP pA) A≅B
 PS⊆SP (pisow{𝑨}{𝑩} pA A≅B) = siso{ov𝓾}{ov𝓾}{P{𝓤}{ov𝓾} 𝒦}{𝑨}{𝑩} (PS⊆SP pA) A≅B

\end{code}

#### <a id="more-class-inclusions">More class inclusions</a>

We conclude this module with three more inclusion relations that will have bit parts to play in our formal proof of Birkhoff's Theorem.

\begin{code}

P⊆V : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → P{𝓤}{𝓦} 𝒦 ⊆ V{𝓤}{𝓦} 𝒦
P⊆V (pbase x) = vbase x
P⊆V{𝓤} (pliftu x) = vlift (P⊆V{𝓤}{𝓤} x)
P⊆V{𝓤}{𝓦} (pliftw x) = vliftw (P⊆V{𝓤}{𝓦} x)
P⊆V (produ x) = vprodu (λ i → P⊆V (x i))
P⊆V (prodw x) = vprodw (λ i → P⊆V (x i))
P⊆V (pisou x x₁) = visou (P⊆V x) x₁
P⊆V (pisow x x₁) = visow (P⊆V x) x₁

SP⊆V : {𝓤 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)}
 →    S{𝓤 ⊔ 𝓦}{𝓤 ⊔ 𝓦} (P{𝓤}{𝓦} 𝒦) ⊆ V{𝓤}{𝓦} 𝒦
SP⊆V (sbase{𝑨} PCloA) = P⊆V (pisow PCloA lift-alg-≅)
SP⊆V (slift{𝑨} x) = vliftw (SP⊆V x)
SP⊆V{𝓤}{𝓦} {𝒦} (ssub{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V{𝓤}{𝓦} {𝒦} (ssubw{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V spA) B≤A
SP⊆V (siso x x₁) = visow (SP⊆V x) x₁

\end{code}


#### <a id="products-of-classes">Products of classes</a>

Next we formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all algebras in the class S(𝒦) belongs to SP(𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least not to this author) how one expresses the product of an entire class of algebras as a dependent type. Nonetheless, after a number of failed attempts, the right type revealed itself. (Not surprisingly, now that we have it, it seems almost obvious.)

\begin{code}

module class-product {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where

\end{code}

First, we define the type that will serve to index the class (as well as the product of its members), as follows.

\begin{code}

 ℑ : {𝓤 : Universe} →  Pred (Algebra 𝓤 𝑆)(ov 𝓤) → (ov 𝓤) ̇
 ℑ {𝓤} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦

\end{code}

Taking the product over this index type ℑ requires a function like the following, which takes an index (i : ℑ) and returns the corresponding algebra.

\begin{code}

 𝔄 : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → ℑ 𝒦 → Algebra 𝓤 𝑆
 𝔄{𝓤}{𝒦} = λ (i : (ℑ 𝒦)) → ∣ i ∣

\end{code}

Finally, the product of all members of 𝒦 is represented as follows.

\begin{code}

 class-product : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (ov 𝓤) 𝑆
 class-product {𝓤} 𝒦 = ⨅ ( 𝔄{𝓤}{𝒦} )

\end{code}

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

\begin{code}

 class-product' : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (ov 𝓤) 𝑆
 class-product'{𝓤} 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦)) → ∣ i ∣

\end{code}

If `p : 𝑨 ∈ 𝒦`, then we can think of the pair `(𝑨 , p) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p)` (which is obviously `𝑨`) as the projection of the product `⨅ ( 𝔄{𝓤}{𝒦} )` onto the `(𝑨 , p)`-th component.


#### ⨅ S(𝒦) ∈ SP(𝒦)
Finally, we prove the result that plays a leading role in the formal proof of Birkhoff's Theorem---namely, that our newly defined class product ⨅ ( 𝔄{𝓤}{𝒦} ) belongs to SP(𝒦).

As we just saw, the (informal) product ⨅ S(𝒦) of all subalgebras of algebras in 𝒦 is implemented (formally) in the [UALib][] as ⨅ ( 𝔄 {𝓤}{S(𝒦)} ), and our goal is to prove that this product belongs to SP(𝒦). We can do this by first proving that the product belongs to PS(𝒦) (in `class-prod-s-∈-ps`) and then applying the PS⊆SP lemma above.

\begin{code}

module class-product-inclusions {𝓤 : Universe} {𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} where
 open class-product {𝓤 = 𝓤}{𝒦 = 𝒦}
 𝓸𝓿𝓾 : Universe
 𝓸𝓿𝓾 = ov 𝓤

 class-prod-s-∈-ps : class-product (S{𝓤}{𝓤} 𝒦) ∈ (P{𝓸𝓿𝓾}{𝓸𝓿𝓾} (S{𝓤}{𝓸𝓿𝓾} 𝒦))
 class-prod-s-∈-ps = pisou{𝓤 = (𝓸𝓿𝓾)}{𝓦 = (𝓸𝓿𝓾)} psPllA (⨅≅ gfe llA≅A)
  where
   lA llA : ℑ (S{𝓤}{𝓤} 𝒦) → Algebra (𝓸𝓿𝓾) 𝑆
   lA i =  lift-alg (𝔄 i) (𝓸𝓿𝓾)
   llA i = lift-alg (lA i) (𝓸𝓿𝓾)

   slA : ∀ i → (lA i) ∈ S 𝒦
   slA i = siso ∥ i ∥ lift-alg-≅

   psllA : ∀ i → (llA i) ∈ P (S 𝒦)
   psllA i = pbase{𝓤 = (𝓸𝓿𝓾)}{𝓦 = (𝓸𝓿𝓾)} (slA i)

   psPllA : ⨅ llA ∈ P (S 𝒦)
   psPllA = produ{𝓤 = (𝓸𝓿𝓾)}{𝓦 = (𝓸𝓿𝓾)} psllA

   llA≅A : ∀ i → (llA i) ≅ (𝔄 i)
   llA≅A i = Trans-≅ (llA i) (𝔄 i) (sym-≅ lift-alg-≅) (sym-≅ lift-alg-≅)

 -- So, since PS⊆SP, we see that that the product of all subalgebras of a class 𝒦 belongs to SP(𝒦).
 class-prod-s-∈-sp : hfunext(𝓸𝓿𝓾)(𝓸𝓿𝓾) → class-product (S 𝒦) ∈ S(P 𝒦)
 class-prod-s-∈-sp hfe = PS⊆SP{hfe = hfe} class-prod-s-∈-ps

\end{code}

----------------------------

[← UALib.Varieties.EquationalLogic](UALib.Varieties.EquationalLogic.html)
<span style="float:right;">[UALib.Varieties.Preservation →](UALib.Varieties.Preservation.html)</span>

{% include UALib.Links.md %}

