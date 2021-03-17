---
layout: default
title : UALib.Relations.Truncation module (The Agda Universal Algebra Library)
date : 2021-02-23
author: William DeMeo
---

### <a id="truncation">Truncation, Sets, Propositions</a>

This section presents the [UALib.Relations.Truncation][] module of the [Agda Universal Algebra Library][].

Here we discuss **truncation** and **h-sets** (which we just call **sets**).  We first give a brief discussion of standard notions of trunction, and then we describe a viewpoint which seems useful for formalizing mathematics in Agda. Readers wishing to learn more about truncation and proof-relevant mathematics should consult other sources, such as [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of [Martín Escardó's notes][], or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

**Remark**. [Agda][] now has a built in type called [Prop](ttps://agda.readthedocs.io/en/v2.6.1.3/language/prop.html) which may provide some or all of what we develop in this module. However, we have never tried to use it, and it seems we can do without it.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Truncation where

open import Relations.Quotients public

\end{code}

#### <a id="typical-view-of-truncation">Truncation</a>

In general, we may have many inhabitants of a given type, hence (via Curry-Howard) many proofs of a given proposition. For instance, suppose we have a type `X` and an identity relation `_≡ₓ_` on `X` so that, given two inhabitants of `X`, say, `a b : X`, we can form the type `a ≡ₓ b`. Suppose `p` and `q` inhabit the type `a ≡ₓ b`; that is, `p` and `q` are proofs of `a ≡ₓ b`, in which case we write `p q : a ≡ₓ b`. We might then wonder whether and in what sense are the two proofs `p` and `q` the equivalent.

We are asking about an identity type on the identity type `≡ₓ`, and whether there is some inhabitant,
say, `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proofs of `a ≡ₓ b` are the same.
If such a proof exists for all `p q : a ≡ₓ b`, then the proof of `a ≡ₓ b` is unique; as a property of
the types `X` and `≡ₓ`, this is sometimes called **uniqueness of identity proofs**.

Now, perhaps we have two proofs, say, `r s : p ≡ₓ₁ q` that the proofs `p` and `q` are equivalent. Then of course we wonder whether `r ≡ₓ₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof-relevance*) is not useful or desirable.  At that point, say, at level `k`, we would be naturally inclined to assume that there is at most one proof of any identity of the form `p ≡ₓₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (at level `k`).

In [homotopy type theory](https://homotopytypetheory.org), a type `X` with an identity relation `≡ₓ` is called a **set** (or **0-groupoid**) if for every pair `x y : X` there is at most one proof of `x ≡ₓ y`. In other words, the type `X`, along with it's equality type `≡ₓ`, form a *set* if for all `x y : X` there is at most one proof of `x ≡ₓ y`.

This notion is formalized in the [Type Topology][] library using the types `is-set` which is defined using the `is-subsingleton` type that we saw earlier ([Prelude.Inverses][]) as follows.<sup>[1](Relations.Truncation.html#fn1)</sup>.

\begin{code}

module hide-is-set {𝓤 : Universe} where

 is-set : 𝓤 ̇ → 𝓤 ̇
 is-set X = (x y : X) → is-subsingleton (x ≡ y)

open import MGS-Embeddings using (is-set) public

\end{code}

Thus, the pair `(X , ≡ₓ)` forms a set if and only if it satisfies `∀ x y : X → is-subsingleton (x ≡ₓ y)`.

The function [to-Σ-≡](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality), which we will also import, is part of Escardó's characterization of equality in Sigma types described in [this section](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality) of [Escardó's notes][]. It is defined as follows.

\begin{code}

module hide-to-Σ-≡ {𝓤 𝓦 : Universe} where

 to-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓦 ̇ } {σ τ : Σ A}
  →       Σ p ꞉ ∣ σ ∣ ≡ ∣ τ ∣ , (transport A p ∥ σ ∥) ≡ ∥ τ ∥
  →       σ ≡ τ

 to-Σ-≡ (refl {x = x} , refl {x = a}) = refl {x = (x , a)}

open import MGS-Embeddings using (to-Σ-≡) public

\end{code}

We will use `is-embedding`, `is-set`, and `to-Σ-≡` in the next subsection to prove that a monic function into a set is an embedding.


#### <a id="injective-functions-are-set-embeddings">Injective functions are set embeddings</a>

Before moving on to define [propositions](Prelude.Truncation.html#propositions), we discharge an obligation we mentioned but left unfulfilled in the [embeddings](Prelude.Inverses.html#embeddings) section of the [Prelude.Inverses][] module.  Recall, we described and imported the `is-embedding` type, and we remarked that an embedding is not simply a monic function.  However, if we assume that the codomain is truncated so as to have unique identity proofs (i.e., is a set), then we can prove that any monic function into that codomain will be an embedding.  On the other hand, embeddings are always monic, so we will end up with an equivalence.  To prepare for this, we define a type `_⟺_` with which to represent such equivalences.

\begin{code}

_⟺_ : {𝓤 𝓦 : Universe} → 𝓤 ̇ → 𝓦 ̇ → 𝓤 ⊔ 𝓦 ̇
X ⟺ Y = (X → Y) × (Y → X)

module _ {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} where

 monic-is-embedding|sets : (f : A → B) → is-set B → Monic f
                           --------------------------------
  →                        is-embedding f

 monic-is-embedding|sets f Bset fmon b (u , fu≡b) (v , fv≡b) = γ
  where
  fuv : f u ≡ f v
  fuv = ≡-trans fu≡b (fv≡b ⁻¹)

  uv : u ≡ v
  uv = fmon u v fuv

  arg1 : Σ p ꞉ (u ≡ v) , (transport (λ a → f a ≡ b) p fu≡b) ≡ fv≡b
  arg1 = uv , Bset (f v) b (transport (λ a → f a ≡ b) uv fu≡b) fv≡b

  γ : u , fu≡b ≡ v , fv≡b
  γ = to-Σ-≡ arg1

\end{code}

In stating the previous result, we introduce a new convention to which we hope to adhere.  Whenever a result holds only for sets, we will add the special suffix `|sets`, which hopefully calls to mind the standard mathematical notation for the restriction of a function to a subset of its domain.

Embeddings are always monic, so we conclude that when a function's codomain is a set, then that function is an embedding if and only if it is monic.

\begin{code}

 embedding-iff-monic|sets : (f : A → B) → is-set B
                            -------------------------
  →                         is-embedding f ⟺ Monic f

 embedding-iff-monic|sets f Bset = (embedding-is-monic f), (monic-is-embedding|sets f Bset)

\end{code}


#### <a id="propositions">Propositions</a>

Sometimes we will want to assume that a type `X` is a *set*. As we just learned, this means there is at most one proof that two inhabitants of `X` are the same.  Analogously, for predicates on `X`, we may wish to assume that there is at most one proof that an inhabitant of `X` satisfies the given predicate.  If a unary predicate satisfies this condition, then we call it a (unary) **proposition**.  We now define a type that captures this concept.

\begin{code}

module _ {𝓤 : Universe} where

 Pred₁ : 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
 Pred₁ A 𝓦 = Σ P ꞉ (Pred A 𝓦) , ∀ x → is-subsingleton (P x)

\end{code}

Recall that `Pred A 𝓦` is simply the function type `A → 𝓦 ̇`, so `Pred₁` is by definition equal to

`Σ P ꞉ (A → 𝓦 ̇) , ∀ x → is-subsingleton (P x)`.

The principle of **proposition extensionality** asserts that logically equivalent propositions are equivalent.  That is, if we have `P Q : Pred₁` and `∣ P ∣ ⊆ ∣ Q ∣` and `∣ Q ∣ ⊆ ∣ P ∣`, then `P ≡ Q`.  This is formalized as follows (cf. Escardó's discussion of [Propositional extensionality and the powerset](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#250227)).

\begin{code}

prop-ext : (𝓤 𝓦 : Universe) → (𝓤 ⊔ 𝓦) ⁺ ̇
prop-ext 𝓤 𝓦 = ∀ {A : 𝓤 ̇}{P Q : Pred₁ A 𝓦 } → ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

Recall, we defined the relation `_≐_` for predicates as follows: `P ≐ Q = (P ⊆ Q) × (Q ⊆ P)`.  Therefore, if we assume `PropExt A 𝓦 {P}{Q}` holds, then it follows that `P ≡ Q`.

\begin{code}

prop-ext' : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{P Q : Pred₁ A 𝓦}
 →          prop-ext 𝓤 𝓦
            -------------------
 →          ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q

prop-ext' pe hyp = pe (fst hyp) (snd hyp)

\end{code}

Thus, for truncated predicates `P` and `Q`, if `prop-ext` holds, then `(P ⊆ Q) × (Q ⊆ P) → P ≡ Q`, which is a useful extensionality principle.


#### <a id="binary-propositions">Binary propositions</a>

Given a binary relation `R`, it may be necessary or desirable to assume that there is at most one way to prove that a given pair of elements is `R`-related.  If this is true of `R`, then we call `R` a **binary proposition**.<sup>[2](Relations.Truncation.html#fn2)</sup>

As above, we use the `is-subsingleton` type of the [Type Topology][] library to impose this truncation assumption on a binary relation.

\begin{code}

Pred₂ : {𝓤 : Universe} → 𝓤 ̇ → (𝓦 : Universe) → 𝓤 ⊔ 𝓦 ⁺ ̇
Pred₂ A 𝓦 = Σ R ꞉ (Rel A 𝓦) , ∀ x y → is-subsingleton (R x y)

\end{code}

To be clear, the type `Rel A 𝓦` is simply the function type `A → A → 𝓦 ̇`, so

`Pred₂ A 𝓦 = Σ R ꞉ (A → A → 𝓦 ̇) , ∀ x y → is-subsingleton (R x y)`.



#### <a id="quotient-extensionality">Quotient extensionality</a>

We need a (subsingleton) identity type for congruence classes over sets so that we can equate two classes even when they are presented using different representatives.  Proposition extensionality is precisely what we need to accomplish this. (Note that we don't require *function* extensionality here.)

\begin{code}

module _ {𝓤 𝓡 : Universe}{A : 𝓤 ̇}{𝑹 : Pred₂ A 𝓡} where

 class-extensionality : prop-ext 𝓤 𝓡 → {u v : A}
  →                     IsEquivalence ∣ 𝑹 ∣
                        --------------------------------------------
  →                     ∣ 𝑹 ∣ u v  →  [ u ] ∣ 𝑹 ∣ ≡ [ v ] ∣ 𝑹 ∣

 class-extensionality pe {u}{v} Reqv Ruv = γ
  where
   P Q : Pred₁ A 𝓡
   P = (λ a → ∣ 𝑹 ∣ u a) , (λ a → ∥ 𝑹 ∥ u a)
   Q = (λ a → ∣ 𝑹 ∣ v a) , (λ a → ∥ 𝑹 ∥ v a)

   α : [ u ] ∣ 𝑹 ∣ ⊆ [ v ] ∣ 𝑹 ∣
   α ua = fst (/-=̇ Reqv Ruv) ua

   β : [ v ] ∣ 𝑹 ∣ ⊆ [ u ] ∣ 𝑹 ∣
   β va = snd (/-=̇ Reqv Ruv) va

   PQ : P ≡ Q
   PQ = (prop-ext' pe (α , β))

   γ : [ u ] ∣ 𝑹 ∣ ≡ [ v ] ∣ 𝑹 ∣
   γ = ap fst PQ



 to-subtype-⟦⟧ : {C D : Pred A 𝓡}{c : 𝒞 C}{d : 𝒞 D}
  →              (∀ C → is-subsingleton (𝒞{R = ∣ 𝑹 ∣} C))
                 -----------------------------------------
  →              C ≡ D  →  (C , c) ≡ (D , d)

 to-subtype-⟦⟧ {D = D}{c}{d} ssA CD = to-Σ-≡ (CD , ssA D (transport 𝒞 CD c) d)


 class-extensionality' : prop-ext 𝓤 𝓡 → {u v : A}
  →                      (∀ C → is-subsingleton (𝒞 C))
  →                      IsEquivalence ∣ 𝑹 ∣
                         -------------------------
  →                      ∣ 𝑹 ∣ u v  →  ⟦ u ⟧ ≡ ⟦ v ⟧

 class-extensionality' pe {u}{v} ssA Reqv Ruv = γ
  where
   CD : [ u ] ∣ 𝑹 ∣ ≡ [ v ] ∣ 𝑹 ∣
   CD = class-extensionality pe Reqv Ruv

   γ : ⟦ u ⟧ ≡ ⟦ v ⟧
   γ = to-subtype-⟦⟧ ssA CD

\end{code}



#### <a id="continuous-propositions">Continuous propositions</a>


We defined a type called `ConRel` in the [Relations.Continuous][] module to represent relations of arbitrary arity. Naturally, we define the corresponding truncated types, the inhabitants of which we will call **continuous propositions**.

\begin{code}

ConProp : 𝓥 ̇ → 𝓤 ̇ → (𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
ConProp I A 𝓦 = Σ P ꞉ (ConRel I A 𝓦) , ∀ 𝑎 → is-subsingleton (P 𝑎)

con-prop-ext : 𝓥 ̇ → 𝓤 ̇ → (𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
con-prop-ext I A 𝓦 = {P Q : ConProp I A 𝓦 }
 →                    ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

If we assume `con-prop-ext  I A 𝓦` holds for some `I`, `A` and `𝓦`, then we can prove that logically equivalent continuous propositions of type `ConProp I A 𝓦` are equivalent.

\begin{code}

con-prop-ext' : (I : 𝓥 ̇)(A : 𝓤 ̇)(𝓦 : Universe){P Q : ConProp I A 𝓦}
 →              con-prop-ext I A 𝓦
                -------------------
 →              ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q

con-prop-ext' I A 𝓦 pe hyp = pe  ∣ hyp ∣  ∥ hyp ∥

\end{code}

While we're at it, we might as well achieve full generality and define truncated types of **dependent continuous propositions**.

\begin{code}

DepProp : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
DepProp I A 𝓦 = Σ P ꞉ (DepRel I A 𝓦) , ∀ 𝑎 → is-subsingleton (P 𝑎)


dep-prop-ext : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇

dep-prop-ext I A 𝓦 = {P Q : DepProp I A 𝓦 }
 →                    ∣ P ∣ ⊆ ∣ Q ∣ → ∣ Q ∣ ⊆ ∣ P ∣ → P ≡ Q

\end{code}

Applying the extensionality principle for dependent continuous relations is no harder than applying the special cases of this principle defined earlier.

\begin{code}

dep-prop-ext' : (I : 𝓥 ̇)(A : I → 𝓤 ̇)(𝓦 : Universe)
                {P Q : DepProp I A 𝓦} → dep-prop-ext I A 𝓦
                -------------------------------------------
 →              ∣ P ∣ ≐ ∣ Q ∣ → P ≡ Q

dep-prop-ext' I A 𝓦 pe hyp = pe  ∣ hyp ∣  ∥ hyp ∥

\end{code}



-----------------------------------

<sup>1</sup><span class="footnote" id="fn1"> As [Escardó][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>


<sup>2</sup><span class="footnote" id="fn2"> This is another example of proof-irrelevance since, if `R` is a binary proposition and we have two proofs of `R x y`, then we can assume that the proofs are indistinguishable or that any distinctions are irrelevant.</span>


<p></p>
<p></p>

[← Relations.Quotients](Relations.Quotients.html)
<span style="float:right;">[Algebras →](Algebras.html)</span>


{% include UALib.Links.md %}
