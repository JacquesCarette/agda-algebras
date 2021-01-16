---
layout: default
title : UALib.Relations.Binary module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="binary-relation-and-kernel-types">Binary Relation and Kernel Types</a>

This section presents the [UALib.Relations.Binary][] module of the [Agda Universal Algebra Library][].

In set theory, a binary relation on a set `A` is simply a subset of the product `A × A`.  As such, we could model these as predicates over the type `A × A`, or as relations of type `A → A → 𝓡 ̇` (for some universe 𝓡). We define these below.

A generalization of the notion of binary relation is a *relation from* `A` *to* `B`, which we also define below.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Relations.Binary where

open import UALib.Relations.Unary public

module _ {𝓤 : Universe} where

 REL : {𝓡 : Universe} → 𝓤 ̇ → 𝓡 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓡 ⊔ 𝓝 ⁺) ̇
 REL A B 𝓝 = A → B → 𝓝 ̇

 KER : {𝓡 : Universe} {A : 𝓤 ̇ } {B : 𝓡 ̇ } → (A → B) → 𝓤 ⊔ 𝓡 ̇
 KER {𝓡} {A} g = Σ x ꞉ A , Σ y ꞉ A , g x ≡ g y

 KER-pred : {𝓡 : Universe} {A : 𝓤 ̇}{B : 𝓡 ̇} → (A → B) → Pred (A × A) 𝓡
 KER-pred g (x , y) = g x ≡ g y

 Rel : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
 Rel A 𝓝 = REL A A 𝓝

 Rel₀ : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
 Rel₀ A 𝓝 = Σ P ꞉ (A → A → 𝓝 ̇) , ∀ x y → is-subsingleton (P x y)

 KER-rel : {𝓡 : Universe}{A : 𝓤 ̇ } {B : 𝓡 ̇ } → (A → B) → Rel A 𝓡
 KER-rel g x y = g x ≡ g y
\end{code}

#### Examples

\begin{code}
 ker : {A B : 𝓤 ̇ } → (A → B) → 𝓤 ̇
 ker = KER{𝓤}

 ker-rel : {A B : 𝓤 ̇ } → (A → B) → Rel A 𝓤
 ker-rel = KER-rel {𝓤}

 ker-pred : {A B : 𝓤 ̇ } → (A → B) → Pred (A × A) 𝓤
 ker-pred = KER-pred {𝓤}

 --The identity relation.
 𝟎 : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎 {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

 --...as a binary relation...
 𝟎-rel : {A : 𝓤 ̇ } → Rel A 𝓤
 𝟎-rel a b = a ≡ b

 --...as a binary predicate...
 𝟎-pred : {A : 𝓤 ̇ } → Pred (A × A) 𝓤
 𝟎-pred (a , a') = a ≡ a'

 𝟎-pred' : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎-pred' {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥

 --...on the domain of an algebra...

 𝟎-alg-rel : {𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝓤 𝑆} → 𝓤 ̇
 𝟎-alg-rel {𝑨 = 𝑨} = Σ a ꞉ ∣ 𝑨 ∣ , Σ b ꞉ ∣ 𝑨 ∣ , a ≡ b

 -- The total relation A × A
 𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
 𝟏 a b = 𝟙
\end{code}

#### Properties of binary relations

\begin{code}
 reflexive : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 reflexive _≈_ = ∀ x → x ≈ x

 symmetric : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

 transitive : {𝓡 : Universe}{X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

 is-subsingleton-valued : {𝓡 : Universe}{A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-prop (x ≈ y)
\end{code}

#### Syntactic sugar

\begin{code}
_on_ : {𝓤 𝓥 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓥 ̇}{C : 𝓦 ̇}
 →     (B → B → C) → (A → B) → (A → A → C)

_*_ on g = λ x y → g x * g y


_⇒_ : {𝓤 𝓥 𝓦 𝓧 : Universe}{A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →    REL A B 𝓦 → REL A B 𝓧 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ̇

P ⇒ Q = ∀ {i j} → P i j → Q i j

infixr 4 _⇒_


_=[_]⇒_ : {𝓤 𝓥 𝓡 𝓢 : Universe}{A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →        Rel A 𝓡 → (A → B) → Rel B 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇

P =[ g ]⇒ Q = P ⇒ (Q on g)

infixr 4 _=[_]⇒_
\end{code}


--------------------------------------

[← UALib.Relations.Unary](UALib.Relations.Unary.html)
<span style="float:right;">[UALib.Relations.Equivalences →](UALib.Relations.Equivalences.html)</span>

{% include UALib.Links.md %}
