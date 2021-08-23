---
layout: default
title : Overture.Preliminaries module
date : 2021-01-13
author: [agda-algebras development team][]
---

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [agda-algebras][] library.

#### <a id="logical-foundations">Logical foundations</a>

(See also the Foundations module of the [agda-algebras][] library.)

An Agda program typically begins by setting some options and by importing types from existing Agda libraries. Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in [agda-algebras][] begins with the following line.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [agda-algebras][] library.


#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line, and then a list of imports of things used in the module.

\begin{code}
module Overture.Preliminaries where

-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Primitive              using ( _⊔_ ; lsuc )           renaming ( Set to  Type ; lzero to  ℓ₀ )
open import Data.Product                using ( _,_ ; Σ-syntax ; _×_ ) renaming ( proj₁ to fst ; proj₂ to snd )
open import Function.Base               using ( _∘_ ; id )
open import Level                       using ( Level ; Lift ; lift ; lower )
open import Relation.Binary.Structures  using ( IsEquivalence ; IsPartialOrder )
open import Relation.Binary.PropositionalEquality
                                        using    ( _≡_ ; refl ; sym ; trans )

private variable α β : Level

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀

-- The empty type
data 𝟘 : Type ℓ₀ where  -- maybe we should use ⊥ instead ...?

-- The one element type
data 𝟙 : Type ℓ₀ where
 𝟎 : 𝟙

-- the two element type
data 𝟚 : Type ℓ₀ where  -- We could use Bool instead.
 𝟎 : 𝟚                  -- "         " false "   "
 𝟏 : 𝟚                  -- "         " true  "   "

-- the three element type
data 𝟛 : Type ℓ₀ where
 𝟎 : 𝟛
 𝟏 : 𝟛
 𝟐 : 𝟛

\end{code}


#### <a id="projection-notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `proj₁` and `proj₂` representing the first and second projections out of the product.  However, we prefer the shorter names `fst` and `snd`.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥`, respectively. We define these alternative notations for projections out of pairs as follows.

\begin{code}

module _ {A : Type α }{B : A → Type β} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd

 infix  40 ∣_∣
\end{code}

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `A : Type α`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

Let's define some useful syntactic sugar that will make it easier to apply symmetry and transitivity of `≡` in proofs.

\begin{code}

_⁻¹ : {A : Type α} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p

infix  40 _⁻¹

\end{code}

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `sym p` we can use the more intuitive `p ⁻¹`. Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

\begin{code}

_∙_ : {A : Type α}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

𝑖𝑑 : (A : Type α ) → A → A
𝑖𝑑 A = λ x → x

infixl 30 _∙_
\end{code}


#### <a id="pi-types">Pi types</a>

The dependent function type is traditionally denoted with a Pi symbol typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes `(x : A) → B x` for the dependent function type, but may use syntax that is closer to the standard Π notation and made available in Agda as follows.

\begin{code}

Π : {A : Type α } (B : A → Type β ) → Type (α ⊔ β)
Π {A = A} B = (x : A) → B x

Π-syntax : (A : Type α)(B : A → Type β) → Type (α ⊔ β)
Π-syntax A B = Π B

syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
infix 6 Π-syntax

\end{code}

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>

```agda
Type α : Type (lsuc α),   Type(lsuc α) : Type (lsuc (lsuc α)),  etc.
```

This means that the universe `Type α` has type `Type(lsuc α)`, and  `Type(lsuc α)` has type `Type(lsuc (lsuc α))`, and so on.  It is important to note, however, this does *not* imply that  `Type α : Type(lsuc(lsuc α))`. In other words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe levels more precisely, which is nice. On the other hand, a non-cumulative hierarchy can sometimes make for a non-fun proof assistant. Specifically, in certain situations, the non-cumulativity makes it unduly difficult to convince Agda that a program or proof is correct.




#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue described in the previous subsection.  In the [Lifts of algebras section](Algebras.Algebras.html#lifts-of-algebras) of the [Algebras.Algebras][] module we will define a couple domain-specific lifting types which have certain properties that make them useful for resolving universe level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
α != 𝓞 ⊔ 𝓥 ⊔ (lsuc α) when checking that the expression... has type...
</samp>

This error message means that Agda encountered the universe level `lsuc α`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⊔ 𝓥 ⊔ lsuc α` instead.

The general `Lift` record type that we now describe makes these situations easier to deal with. It takes a type inhabiting some universe and embeds it into a higher universe and, apart from syntax and notation, it is equivalent to the `Lift` type one finds in the `Level` module of the [Agda Standard Library][].

```agda
 record Lift {𝓦 α : Level} (A : Type α) : Type (α ⊔ 𝓦) where
  constructor lift
  field lower : A
```

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

\begin{code}

lift∼lower : {A : Type α} → lift ∘ lower ≡ 𝑖𝑑 (Lift β A)
lift∼lower = refl

lower∼lift : {A : Type α} → (lower {α}{β}) ∘ lift ≡ 𝑖𝑑 A
lower∼lift = refl

\end{code}

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.


#### <a id="pointwise-equality-of-dependent-functions">Pointwise equality of dependent functions</a>

We conclude this module with a definition that conveniently represents te assertion that two functions are (extensionally) the same in the sense that they produce the same output when given the same input.  (We will have more to say about this notion of equality in the [Relations.Extensionality][] module.)

\begin{code}

module _ {α : Level}{A : Type α}{β : Level}{B : A → Type β } where

 _≈_ :  (f g : (a : A) → B a) → Type (α ⊔ β)
 f ≈ g = ∀ x → f x ≡ g x

 infix 8 _≈_

 ≈IsEquivalence : IsEquivalence _≈_
 IsEquivalence.refl ≈IsEquivalence = λ _ → refl
 IsEquivalence.sym ≈IsEquivalence {f}{g} f≈g = λ x → sym (f≈g x)
 IsEquivalence.trans ≈IsEquivalence {f}{g}{h} f≈g g≈h = λ x → trans (f≈g x) (g≈h x)

\end{code}

The following is convenient for proving two pairs of a product type are equal using the fact that their
respective components are equal.

\begin{code}

≡-by-parts : {A : Type α}{B : Type β}{u v : A × B} → fst u ≡ fst v → snd u ≡ snd v → u ≡ v
≡-by-parts refl refl = refl

\end{code}

Lastly, we will use the following type (instead of `subst`) to transport equality proofs.

\begin{code}

transport : {A : Type α } (B : A → Type β) {x y : A} → x ≡ y → B x → B y
transport B refl = id

\end{code}


------------------------------

<br>
<br>

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Inverses →](Overture.Inverses.html)</span>



{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team

[agda-algebras]: https://github.com/ualib/agda-algebras


