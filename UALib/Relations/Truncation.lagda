---
layout: default
title : UALib.Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation</a>

This section presents the [UALib.Relations.Truncation][] module of the [Agda Universal Algebra Library][].

Here we discuss **truncation** and **h-sets** (which we just call **sets**).  We first give a brief discussion of standard notions of trunction, and then we describe a viewpoint which seems useful for formalizing mathematics in Agda. Readers wishing to learn more about truncation and proof-relevant mathematics should consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Truncation where

open import Relations.Quotients public

module _ {𝓤 : Universe} where

\end{code}

#### <a id="a-typical-view-of-truncation">A typical view of truncation</a>

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given proposition. For instance, suppose we have a type `X` and an identity relation `_≡ₓ_` on `X` so that, given two inhabitants of `X`, say, `a b : X`, we can form the type `a ≡ₓ b`. Suppose `p` and `q` inhabit the type `a ≡ₓ b`; that is, `p` and `q` are proofs of `a ≡ₓ b`, in which case we write `p q : a ≡ₓ b`. We might then wonder whether and in what sense are the two proofs `p` and `q` the equivalent. We are asking about an identity type on the identity type `≡ₓ`, and whether there is some inhabitant, say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡ₓ b` are the same.  If such a proof exists for all `p q : a ≡ₓ b, then we say that the proof of `a ≡ₓ b` is *unique*. As a property of the types `X` and `≡ₓ`, this is sometimes called **uniqueness of identity proofs**.

Perhaps we have two proofs, say, `r s : p ≡ₓ₁ q` that the proofs `p` and `q` are equivalent. Then of course we will ask whether `r ≡ₓ₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₓₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).

In [homotopy type theory](https://homotopytypetheory.org), a type `X` with an identity relation `≡ₓ` is called a **set** (or **0-groupoid**) if for every pair `x y : X` there is at most one proof of `x ≡ₓ y`. In other words, the type `X`, along with it's equality type `≡ₓ`, form a *set* if for all `x y : X` there is at most one proof of `x ≡ₓ y`.

This notion is formalized in the [TypeTopology][] library using the types `is-set` and `is-subsingleton`, which are defined as follows.<span class="footnote"><sup>1</sup></span>

\begin{code}

module hide-is-set {𝓤 : Universe} where
 is-subsingleton : 𝓤 ̇ → 𝓤 ̇
 is-subsingleton X = (x y : X) → x ≡ y

 is-set : 𝓤 ̇ → 𝓤 ̇
 is-set X = (x y : X) → is-subsingleton (x ≡ y)

\end{code}

Using the `is-subsingleton` function from the [TypeTopology][] library, the pair `(X , ≡ₓ)` forms a set if and only if it satisfies

`∀ x y : X → is-subsingleton (x ≡ₓ y)`.


#### <a id="predicate-truncation">Predicate truncation</a>

Above we learned the about the concepts of *truncation* and *set* of proof-relevant mathematics. Sometimes we will want to assume that a type is a *set*. Recall, this mean there is at most one proof that two elements are the same. Analogously, for predicates, we may wish to assume that there is at most one proof that a given element satisfies a given predicate.  We call a predicate *truncated* if it satisfies this condition.

\begin{code}

open import MGS-Powerset using (propext)
open import MGS-Subsingleton-Theorems using (dfunext; is-subsingleton)

Pred₀ : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
Pred₀ A 𝓦 = Σ P ꞉ (A → 𝓦 ̇) , ∀ x → is-subsingleton (P x)

\end{code}

The next lemma reveals why sometimes want our predicates to be truncated.

\begin{code}

Pred-=̇-≡ : {𝓧 𝓨 : Universe} → propext 𝓨 → dfunext 𝓧 (𝓨 ⁺)
 →         {A : 𝓧 ̇}{P Q : Pred A 𝓨}
 →         (∀ x → is-subsingleton (P x))
 →         (∀ x → is-subsingleton (Q x))
           -----------------------------
 →         P =̇ Q → P ≡ Q

Pred-=̇-≡ pe fe {A}{P}{Q} ssP ssQ (pq , qp) = fe γ
 where
  γ : ∀ x → P x ≡ Q x
  γ x = pe (ssP x) (ssQ x) pq qp

\end{code}

Thus, for truncated predicates, we can actually prove that `P ⊆ Q × Q ⊆ P → P ≡ Q`, which is a useful extensionality principle.


#### <a id="Relation-truncation">Relation truncation</a>

Given a binary relation `R`, it may be necessary or desirable to assume that there is at most one way to prove that a given pair of elements is `R`-related.  If this is true of `R`, then we call `R` a *truncated binary relation*.  This is another example of proof-irrelevance since, if `R` is truncated and we have two proofs of `R x y`, then we can assume that the proofs are indistinguishable or that any distinctions are irrelevant.

As above, we enforce this truncation assumption using the `is-subsingleton` type of the [Type Topology][] library.

\begin{code}

Rel₀ : 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
Rel₀ A 𝓝 = Σ R ꞉ (A → A → 𝓝 ̇) , ∀ x y → is-subsingleton (R x y)

\end{code}

#### <a id="quotient-extensionality">Quotient extensionality</a>

We need a (subsingleton) identity type for congruence classes over sets so that we can equate two classes even when they are presented using different representatives.  For this we assume that our relations are truncated.  We say the binary relation `R : A → A → 𝓡` is truncated if for all `x y : A` there is at most one proof of `R x y`.

\begin{code}

module _ {𝓤 𝓡 : Universe} {A : 𝓤 ̇}{R : Rel A 𝓡} where

 class-extensionality : propext 𝓡 → dfunext 𝓤 (𝓡 ⁺) → {a a' : A}
  →                     (∀ a x → is-subsingleton (R a x)) → IsEquivalence R
                        ----------------------------------------------------
  →                     R a a'  →  [ a ] R  ≡  [ a' ] R

 class-extensionality pe fe {a}{a'} ssR Req Raa' = Pred-=̇-≡ pe fe (ssR a)(ssR a')(/-=̇ Req Raa')


 open import MGS-MLTT using (transport)

 to-subtype-⟦⟧ : {C D : Pred A 𝓡}{c : 𝒞 C}{d : 𝒞 D} 
  →              (∀ C → is-subsingleton (𝒞{R = R} C))
                 -------------------------------------
  →              C ≡ D  →  (C , c) ≡ (D , d)

 to-subtype-⟦⟧ {D = D}{c}{d} ssA CD = to-Σ-≡ (CD , ssA D (transport 𝒞 CD c) d)


 class-extensionality' : propext 𝓡 → dfunext 𝓤 (𝓡 ⁺) → {a a' : A}
  →                      (∀ a x → is-subsingleton (R a x))
  →                      (∀ C → is-subsingleton (𝒞 C))
  →                      IsEquivalence R
                         -------------------------
  →                      R a a'  →  ⟦ a ⟧ ≡ ⟦ a' ⟧

 class-extensionality' pe fe {a}{a'} ssR ssA Req Raa' = γ
  where
   CD : [ a ] R ≡ [ a' ] R
   CD = class-extensionality pe fe ssR Req Raa'

   γ : ⟦ a ⟧ ≡ ⟦ a' ⟧
   γ = to-subtype-⟦⟧ ssA CD

\end{code}




-----------------------------------

<span class="footnote"><sup>1</sup>As [Escardó][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>

----------------------------------------

[← Relations.Quotients](Relations.Quotients.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}

