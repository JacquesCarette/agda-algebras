---
layout: default
title : Subalgebras.Subalgebras module (The Agda Universal Algebra Library)
date : 2021-01-14
author: [agda-algebras development team][]
---

### <a id="subalgebras">Subalgebras</a>

The [Subalgebras.Subalgebras][] module of the [Agda Universal Algebra Library][] defines the `Subalgebra` type, representing the subalgebra of a given algebra, as well as the collection of all subalgebras of a given class of algebras.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using (𝓞 ; 𝓥 ; Signature )

module Subalgebras.Subalgebras {𝑆 : Signature 𝓞 𝓥} where

-- imports from Agda and the Agda Standard Library ------------------------------------
open import Agda.Builtin.Equality using ( _≡_ ; refl )
open import Agda.Primitive        using ( _⊔_ ; lsuc ; Level )       renaming ( Set to Type )
open import Data.Product          using ( _,_ ; Σ-syntax ; Σ ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base         using ( _∘_ )
open import Function.Bundles      using ( Injection )
open import Relation.Unary        using ( _∈_ ; Pred ; _⊆_ )
import Relation.Binary.PropositionalEquality as PE

-- imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries             using ( _∙_ ; _⁻¹ ; ∣_∣ ; ∥_∥ ; 𝑖𝑑 )
open import Overture.Inverses                  using ( ∘-injective ; IsInjective ; id-is-injective )
open import Relations.Truncation               using ( is-set ; blk-uip )
open import Relations.Extensionality           using ( swelldef ; pred-ext )
open import Algebras.Basic                     using ( Algebra ; Lift-Alg )
open import Algebras.Products          {𝑆 = 𝑆} using ( ov )
open import Homomorphisms.Basic        {𝑆 = 𝑆} using ( hom ; kercon ; ker[_⇒_]_↾_ ; ∘-hom ; is-homomorphism ; ∘-is-hom ; 𝒾𝒹 )
open import Homomorphisms.Noether      {𝑆 = 𝑆} using ( FirstHomTheorem|Set )
open import Homomorphisms.Isomorphisms {𝑆 = 𝑆} using ( _≅_ ; ≅-sym ; ≅-trans ; Lift-≅ ; mkiso ; ≅toInjective ; ≅fromInjective )
open import Terms.Basic                {𝑆 = 𝑆} using ( Term ; ℊ ; node ; 𝑻 )

private variable α β γ 𝓧 : Level
\end{code}


#### <a id="subalgebra-type">Subalgebra type</a>

Given algebras `𝑨 : Algebra α 𝑆` and `𝑩 : Algebra 𝓦 𝑆`, we say that `𝑩` is a **subalgebra** of `𝑨` just in case `𝑩` can be *homomorphically embedded* in `𝑨`; that is, there exists a map `h : ∣ 𝑩 ∣ → ∣ 𝑨 ∣` that is both a homomorphism and an embedding.<sup>[1](Subalgebras.Subalgebras.html#fn1)</sup>

\begin{code}

_≤_  -- (alias for subalgebra relation))
 _IsSubalgebraOf_ : Algebra α 𝑆 → Algebra β 𝑆 → Type _
𝑨 IsSubalgebraOf 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

_≥_  -- (alias for supalgebra (aka overalgebra))
 _IsSupalgebraOf_ : Algebra α 𝑆 → Algebra β 𝑆 → Type _
𝑨 IsSupalgebraOf 𝑩 = Σ[ h ∈ hom 𝑩 𝑨 ] IsInjective ∣ h ∣

-- Syntactic sugar for sub/sup-algebra relations.
𝑨 ≤ 𝑩 = 𝑨 IsSubalgebraOf 𝑩
𝑨 ≥ 𝑩 = 𝑨 IsSupalgebraOf 𝑩

-- From now on we use `𝑨 ≤ 𝑩` to express the assertion that `𝑨` is a subalgebra of `𝑩`.


record SubalgebraOf : Type (ov (α ⊔ β)) where
 field
  algebra : Algebra α 𝑆
  subalgebra : Algebra β 𝑆
  issubalgebra : subalgebra ≤ algebra


Subalgebra : Algebra α 𝑆 → {β : Level} → Type _
Subalgebra  𝑨 {β} = Σ[ 𝑩 ∈ (Algebra β 𝑆) ] 𝑩 ≤ 𝑨


\end{code}



Note the order of the arguments.  The universe `β` comes first because in certain situations we must explicitly specify this universe, whereas we can almost always leave the universe `α` implicit. (See, for example, the definition of `_IsSubalgebraOfClass_` below.)




#### <a id="consequences-of-first-homomorphism-theorem">Consequences of First Homomorphism Theorem</a>

We take this opportunity to prove an important lemma that makes use of the `IsSubalgebraOf` type defined above.  It is the following: If `𝑨` and `𝑩` are `𝑆`-algebras and `h : hom 𝑨 𝑩` a homomorphism from `𝑨` to `𝑩`, then the quotient `𝑨 ╱ ker h` is (isomorphic to) a subalgebra of `𝑩`.  This is an easy corollary of the First Homomorphism Theorem proved in the [Homomorphisms.Noether][] module.

\begin{code}

module _ (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆)(h : hom 𝑨 𝑩)
         -- extensionality assumptions:
         (pe : pred-ext α β)(fe : swelldef 𝓥 β)

         -- truncation assumptions:
         (Bset : is-set ∣ 𝑩 ∣)
         (buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣)
         where

 FirstHomCorollary|Set : (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) IsSubalgebraOf 𝑩
 FirstHomCorollary|Set = ϕhom , ϕinj
  where
   hh = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip
   ϕhom : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩
   ϕhom = ∣ hh ∣

   ϕinj : IsInjective ∣ ϕhom ∣
   ϕinj = ∣ snd ∥ hh ∥ ∣

\end{code}

If we apply the foregoing theorem to the special case in which the `𝑨` is term algebra `𝑻 X`, we obtain the following result which will be useful later.

\begin{code}

module _ (X : Type 𝓧)(𝑩 : Algebra β 𝑆)(h : hom (𝑻 X) 𝑩)
         -- extensionality assumptions:
         (pe : pred-ext (ov 𝓧) β)(fe : swelldef 𝓥 β)

         -- truncation assumptions:
         (Bset : is-set ∣ 𝑩 ∣)
         (buip : blk-uip (Term X) ∣ kercon fe {𝑩} h ∣)
         where

 free-quot-subalg : (ker[ 𝑻 X ⇒ 𝑩 ] h ↾ fe) IsSubalgebraOf 𝑩
 free-quot-subalg = FirstHomCorollary|Set{α = ov 𝓧}(𝑻 X) 𝑩 h pe fe Bset buip

\end{code}

#### <a id="subalgebras-of-a-class">Subalgebras of a class</a>

One of our goals is to formally express and prove properties of classes of algebraic structures.  Fixing a signature `𝑆` and a universe `α`, we represent classes of `𝑆`-algebras with domains of type `Type α` as predicates over the `Algebra α 𝑆` type. In the syntax of the [UniversalAlgebra][] library, such predicates inhabit the type `Pred (Algebra α 𝑆) γ`, for some universe γ.

Suppose `𝒦 : Pred (Algebra α 𝑆) γ` denotes a class of `𝑆`-algebras and `𝑩 : Algebra β 𝑆` denotes an arbitrary `𝑆`-algebra. Then we might wish to consider the assertion that `𝑩` is a subalgebra of an algebra in the class `𝒦`.  The next type we define allows us to express this assertion as `𝑩 IsSubalgebraOfClass 𝒦`.

\begin{code}

module _ {α β : Level} where

 _IsSubalgebraOfClass_ : Algebra β 𝑆 → Pred (Algebra α 𝑆) γ → Type (γ ⊔ ov (α ⊔ β))
 𝑩 IsSubalgebraOfClass 𝒦 = Σ[ 𝑨 ∈ Algebra α 𝑆 ] Σ[ sa ∈ Subalgebra 𝑨 {β} ] ((𝑨 ∈ 𝒦) × (𝑩 ≅ ∣ sa ∣))

\end{code}

Using this type, we express the collection of all subalgebras of algebras in a class by the type `SubalgebraOfClass`, which we now define.

\begin{code}

 SubalgebraOfClass : Pred (Algebra α 𝑆)(ov α) → Type (ov (α ⊔ β))
 SubalgebraOfClass 𝒦 = Σ[ 𝑩 ∈ Algebra β 𝑆 ] 𝑩 IsSubalgebraOfClass 𝒦

\end{code}

------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
