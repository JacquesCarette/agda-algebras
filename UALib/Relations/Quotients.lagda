---
layout: default
title : UALib.Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="quotient-types">Quotient Types</a>

This section presents the [UALib.Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Relations.Quotients where

open import UALib.Relations.Equivalences public
open import UALib.Prelude.Preliminaries using (_⇔_; id) public

\end{code}

For a binary relation `R` on `A`, we denote a single R-class as `[ a ] R` (the class containing `a`). This notation is defined in UALib as follows.

\begin{code}
module _ {𝓤 𝓡 : Universe} where

 -- relation class
 [_] : {A : 𝓤 ̇ } → A → Rel A 𝓡 → Pred A 𝓡
 [ a ] R = λ x → R a x

\end{code}

So, `x ∈ [ a ] R` iff `R a x`, as desired.

We define type of all classes of a relation `R` as follows.

\begin{code}

 𝒞 : {A : 𝓤 ̇}{R : Rel A 𝓡} → Pred A 𝓡 → (𝓤 ⊔ 𝓡 ⁺) ̇
 𝒞 {A}{R} = λ (C : Pred A _) → Σ a ꞉ A , C ≡ ( [ a ] R)

\end{code}

There are a few ways we could define the quotient with respect to a relation. We have found the following to be the most convenient.

\begin{code}

 -- relation quotient (predicate version)
 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓡 → 𝓤 ⊔ (𝓡 ⁺) ̇
 A / R = Σ C ꞉ Pred A _ ,  𝒞{A}{R} C

\end{code}

We then define the following introduction rule for a relation class with designated representative.

\begin{code}

 ⟦_⟧ : {A : 𝓤 ̇} → A → {R : Rel A 𝓡} → A / R
 ⟦ a ⟧ {R} = ([ a ] R) , a , 𝓇ℯ𝒻𝓁

\end{code}

So, x ∈ [ a ]ₚ R iff R a x, as desired.

If the relation is reflexive, then we have the following elimination rules.

\begin{code}

 /-refl : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡} → reflexive R → [ a ] R ≡ [ a' ] R → R a a'

 /-refl{A}{a}{a'}{R} rfl x  = cong-app-pred a' (rfl a') (x ⁻¹)


 ⌜_⌝ : {A : 𝓤 ̇}{R : Rel A 𝓡} → A / R  → A

 ⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

\end{code}

Later we will need the following additional quotient tools.

\begin{code}

module _ {𝓤 𝓡 : Universe} where

 open IsEquivalence{𝓤}{𝓡}

 /-subset : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) ⊆ ([ a' ] R)
 /-subset {A = A}{a}{a'}{R} Req Raa' {x} Rax = (trans Req) a' a x (sym Req a a' Raa') Rax

 /-supset : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) ⊇ ([ a' ] R)
 /-supset {A = A}{a}{a'}{R} Req Raa' {x} Ra'x = (trans Req) a a' x Raa' Ra'x

 /-=̇ : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) =̇ ([ a' ] R)
 /-=̇ {A = A}{a}{a'}{R} Req Raa' = /-subset Req Raa' , /-supset Req Raa'

\end{code}

#### <a id="quotient-extensionality">Quotient extensionality</a>

We need a (subsingleton) identity type for congruence classes over sets so that we can equate two classes even when they are presented using different representatives.  For this we assume that our relations are on sets, rather than arbitrary types.  As mentioned earlier, this is equivalent to assuming that there is at most one proof that two elements of a set are the same.

(Recall, a type is called a **set** if it has *unique identity proofs*; as a general principle, this is sometimes referred to as "proof irrelevance" or "uniqueness of identity proofs"---two proofs of a single identity are the same.)

\begin{code}

class-extensionality : {𝓤 𝓡 : Universe} → propext 𝓡 → global-dfunext
 →                     {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
 →                     (∀ a x → is-subsingleton (R a x))
 →                     IsEquivalence R
                       -------------------------------
 →                     R a a' → ([ a ] R) ≡ ([ a' ] R)

class-extensionality pe gfe {A = A}{a}{a'} ssR Req Raa' = Pred-=̇-≡ pe gfe (ssR a)(ssR a')(/-=̇ Req Raa')


to-subtype-⟦⟧ : {𝓤 𝓡 : Universe}{A : 𝓤 ̇}{R : Rel A 𝓡}{C D : Pred A 𝓡}
                {c : 𝒞 C}{d : 𝒞 D}
 →              (∀ C → is-subsingleton (𝒞{R = R} C))
 →              C ≡ D  →  (C , c) ≡ (D , d)

to-subtype-⟦⟧ {D = D}{c}{d} ssA CD = to-Σ-≡ (CD , ssA D (transport 𝒞 CD c) d)


class-extensionality' : {𝓤 𝓡 : Universe} → propext 𝓡 → global-dfunext → {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
 →                      (∀ a x → is-subsingleton (R a x)) → (∀ C → is-subsingleton (𝒞 C))
 →                      IsEquivalence R
                        -----------------------------------
 →                      R a a' → (⟦ a ⟧ {R}) ≡ (⟦ a' ⟧ {R})

class-extensionality' pe gfe {A = A}{a}{a'}{R} ssR ssA Req Raa' = γ
 where
  CD : ([ a ] R) ≡ ([ a' ] R)
  CD = class-extensionality pe gfe ssR Req Raa'

  γ : (⟦ a ⟧ {R}) ≡ (⟦ a' ⟧ {R})
  γ = to-subtype-⟦⟧ ssA CD

\end{code}


#### <a id="compatibility-of-lifts-and-functions">Compatibility of lifts and functions</a>

Finally, we define some types that are useful for asserting and proving facts about *compatibility* of relations and functions.

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe} {γ : 𝓥 ̇} {Z : 𝓤 ̇} where

 lift-rel : Rel Z 𝓦 → (γ → Z) → (γ → Z) → 𝓥 ⊔ 𝓦 ̇
 lift-rel R f g = ∀ x → R (f x) (g x)

 compatible-fun : (f : (γ → Z) → Z)(R : Rel Z 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

\end{code}



--------------------------------------

[← UALib.Relations.Equivalences](UALib.Relations.Equivalences.html)
<span style="float:right;">[UALib.Algebras.Signatures →](UALib.Algebras.Signatures.html)</span>

{% include UALib.Links.md %}
