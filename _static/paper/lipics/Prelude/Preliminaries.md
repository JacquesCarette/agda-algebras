---
layout: default
title : UALib.Prelude.Preliminaries module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

<!--
FILE: Preliminaries.lagda
AUTHOR: William DeMeo
DATE: 14 Jan 2021
REF: Parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
     Below, MHE = Martin Hötzel Escardo.
-->

### <a id="preliminaries">Preliminaries</a>

This section describes the [UALib.Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

**Notation**. Here are some acronyms that we use frequently.

  * MHE = [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe/)
  * MLTT = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)

---------------------------------

#### <a id="options">Options</a>

All Agda programs begin by setting some options and by importing from existing libraries (in our case, the [Agda Standard Library][] and the [Type Topology][] library by MHE). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, each Agda source code file in the UALib begins with the following line:

\begin{code}%
\>[0]\<%
\\
\>[0]\AgdaSymbol{\{-\#}\AgdaSpace{}%
\AgdaKeyword{OPTIONS}\AgdaSpace{}%
\AgdaPragma{--without-K}\AgdaSpace{}%
\AgdaPragma{--exact-split}\AgdaSpace{}%
\AgdaPragma{--safe}\AgdaSpace{}%
\AgdaSymbol{\#-\}}\<%
\\
\>[0]\<%
\end{code}

These options control certain foundational assumptions that Agda assumes when type-checking the program to verify its correctness.

* `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities.  MHE explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`; we would use the following `OPTIONS` line in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

but this is never done in publicly released versions of the UALib.

---------------------------------

#### <a id="modules">Modules</a>

The `OPTIONS` line is usually followed by the start of a module.  For example, here's how we start the Preliminaries module here.

\begin{code}%
\>[0]\<%
\\
\>[0]\AgdaKeyword{module}\AgdaSpace{}%
\AgdaModule{UALib.Prelude.Preliminaries}\AgdaSpace{}%
\AgdaKeyword{where}\<%
\\
\>[0]\<%
\end{code}

Sometimes we may wish to pass in parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module.  We'll see many examples later, but as a preview,

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where
```

is how we often start an (anonymous) module in which the fixed signature 𝑆 will be assumed until the end of the module. (The module started with the line above would be anonymous because the underscore `_` appears instead of a module name.)

Agda determines where a model begins and ends by indentation.  This can take some getting used to, but after a short time it will seem quite natural.

The main module of a file must have the same name as the file (without the trailing `.agda` or `.lagda`, of course).  The code inside the main module is not indented. Modules may be declared inside the main module and code inside these submodules must be indented to the same column.  As long as the code is indented, Agda considers it part of the submodule.  To exit the submodule, we return to nonindented code.  So, the general pattern is as follows:

```agda

module main where

a-function-in-the-main-module : {𝓤 : Universe}{A B : 𝓤 ̇} → A → B
a-function-in-the-main-module = λ a → a

module _ {𝓤 : Universe} where

 a-function-inside-an-anonymous-submodule : {A B : 𝓤 ̇} → A → B
 a-function-inside-an-anonymous-submodule = λ a → a

a-function-outside-the-submodule : {A B : 𝓤 ̇} → A → B
a-function-outside-the-submodule a = a
```

Actually, for illustration purposes, the example we gave here is not one that Agda would normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope. In the UAlib, however, we tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.

----------------------------------

#### <a id="imports-from-type-topology">Imports from Type Topology</a>

Throughout we use many of the nice tools that [Martin Escardo][] has developed and made available in the [Type Topology][] repository of Agda code for the "Univalent Foundations" of mathematics.

We import these now.

\begin{code}%
\>[0]\<%
\\
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{universes}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{Identity-Type}\AgdaSpace{}%
\AgdaKeyword{renaming}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaOperator{\AgdaDatatype{\AgdaUnderscore{}≡\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{to}\AgdaSpace{}%
\AgdaKeyword{infix}\AgdaSpace{}%
\AgdaNumber{0}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{\AgdaUnderscore{}≡\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{;}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\AgdaSpace{}%
\AgdaSymbol{to}\AgdaSpace{}%
\AgdaInductiveConstructor{𝓇ℯ𝒻𝓁}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{pattern}\AgdaSpace{}%
\AgdaInductiveConstructor{refl}\AgdaSpace{}%
\AgdaBound{x}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaInductiveConstructor{𝓇ℯ𝒻𝓁}\AgdaSpace{}%
\AgdaSymbol{\{}x \AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{x}\AgdaSymbol{\}}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{Sigma-Type}\AgdaSpace{}%
\AgdaKeyword{renaming}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaOperator{\AgdaInductiveConstructor{\AgdaUnderscore{},\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{to}\AgdaSpace{}%
\AgdaKeyword{infixr}\AgdaSpace{}%
\AgdaNumber{50}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{\AgdaUnderscore{},\AgdaUnderscore{}}}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-MLTT}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}∘\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{domain}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{codomain}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{transport}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}≡⟨\AgdaUnderscore{}⟩\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}∎}}\AgdaSymbol{;}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[1]\AgdaFunction{pr₁}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{pr₂}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{-Σ}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{𝕁}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{Π}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{¬}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}×\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{𝑖𝑑}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}∼\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{\AgdaUnderscore{}+\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{𝟘}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{𝟙}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{𝟚}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}⇔\AgdaUnderscore{}}}\AgdaSymbol{;}\<%
\\
%
\>[1]\AgdaFunction{lr-implication}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{rl-implication}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{id}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}⁻¹}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{ap}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-Equivalences}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{is-equiv}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{inverse}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{invertible}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-Subsingleton-Theorems}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{funext}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{global-hfunext}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{dfunext}\AgdaSymbol{;}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[1]\AgdaFunction{is-singleton}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{is-subsingleton}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{is-prop}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{Univalence}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{global-dfunext}\AgdaSymbol{;}\<%
\\
%
\>[1]\AgdaFunction{univalence-gives-global-dfunext}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}●\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}≃\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{Π-is-subsingleton}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{Σ-is-subsingleton}\AgdaSymbol{;}\<%
\\
%
\>[1]\AgdaFunction{logically-equivalent-subsingletons-are-equivalent}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-Powerset}\AgdaSpace{}%
\AgdaKeyword{renaming}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}∈\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{to}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}∈₀\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}⊆\AgdaUnderscore{}}}\AgdaSpace{}%
\AgdaSymbol{to}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}⊆₀\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{∈-is-subsingleton}\AgdaSpace{}%
\AgdaSymbol{to}\AgdaSpace{}%
\AgdaFunction{∈₀-is-subsingleton}\AgdaSymbol{)}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[1]\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{𝓟}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{equiv-to-subsingleton}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{powersets-are-sets'}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{subset-extensionality'}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{propext}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}holds}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{Ω}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-Embeddings}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{Nat}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{NatΠ}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{NatΠ-is-embedding}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{is-embedding}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{pr₁-embedding}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{∘-embedding}\AgdaSymbol{;}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[1]\AgdaFunction{is-set}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}↪\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{embedding-gives-ap-is-equiv}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{embeddings-are-lc}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{×-is-subsingleton}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{id-is-embedding}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-Solved-Exercises}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{to-subtype-≡}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-Unique-Existence}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{∃!}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{-∃!}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{MGS-Subsingleton-Truncation}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}∙\AgdaUnderscore{}}}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{to-Σ-≡}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{equivs-are-embeddings}\AgdaSymbol{;}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[1]\AgdaFunction{invertibles-are-equivs}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{fiber}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{⊆-refl-consequence}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{hfunext}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
\>[0]\<%
\end{code}

Notice that we carefully specify which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes explicit which components of the type theory we are using.

-------------------------

#### <a id="agda-universes">Special notation for Agda universes</a>

The first import in the list of `open import` directives above imports the `universes` module from MHE's [Type Topology][] library. This provides, among other things, an elegant notation for type universes that we have fully adopted and we use it throughout the Agda UALib.

[MHE][] has authored an outstanding set of notes called [Introduction to Univalent Foundations of Mathematics with Agda][]. We highly recommend these notes to anyone wanting more details than we provide here about MLTT and the Univalent Foundations/HoTT extensions thereof.

Following MHE, we refer to universes using capitalized script letters from near the end of the alphabet, e.g., 𝓤, 𝓥, 𝓦, 𝓧, 𝓨, 𝓩, etc.

Also in the `Universes` module MHE defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero` (which, incidentally, corresponds to `Sort 0` in the [Lean][] proof assistant language).<sup>1</sup>

Thus, 𝓤 ̇ is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`.

Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we (and MHE) denote by `𝓤₀ ⁺ ̇`.

The following dictionary translates between standard Agda syntax and MHE/UALib notation.

```agda
Agda              MHE and UALib
====              ==============
Level             Universe
lzero             𝓤₀
𝓤 : Level         𝓤 : Universe
Set lzero         𝓤₀ ̇
Set 𝓤             𝓤 ̇
lsuc lzero        𝓤₀ ⁺
lsuc 𝓤            𝓤 ⁺
Set (lsuc lzero)  𝓤₀ ⁺ ̇
Set (lsuc 𝓤)      𝓤 ⁺ ̇
Setω              𝓤ω
```

To justify the introduction of this somewhat nonstandard notation for universe levels, MHE points out that the Agda library uses `Level` for universes (so what we write as 𝓤 ̇ is written `Set 𝓤` in standard Agda), but in univalent mathematics the types in 𝓤 ̇ need not be sets, so the standard Agda notation can be misleading.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, 𝓤 ̇ and 𝓥 ̇ . The universe 𝓤 ⊔ 𝓥 ̇ denotes this least upper bound. Here 𝓤 ⊔ 𝓥 is used to denote the universe level corresponding to the least upper bound of the levels 𝓤 and 𝓥, where the `_⊔_` is an Agda primitive designed for precisely this purpose.

--------------------

#### <a id="dependent-pair-type">Dependent pair type</a>

Our preferred notations for the first and second projections of a product are `∣_∣` and `∥_∥`, respectively; however, we will sometimes use more standard alternatives, such as `pr₁` and `pr₂`, or `fst` and `snd`, for emphasis, readability, or compatibility with other libraries.

\begin{code}%
\>[0]\<%
\\
\>[0]\AgdaKeyword{module}\AgdaSpace{}%
\AgdaModule{\AgdaUnderscore{}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{𝓤}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPostulate{Universe}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaKeyword{where}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[1]\AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}}\AgdaSpace{}%
\AgdaFunction{fst}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{X}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{𝓤}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{̇}}\AgdaSpace{}%
\AgdaSymbol{\}\{}\AgdaBound{Y}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{X}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaGeneralizable{𝓥}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{̇}}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaRecord{Σ}\AgdaSpace{}%
\AgdaBound{Y}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaBound{X}\<%
\\
%
\>[1]\AgdaOperator{\AgdaFunction{∣}}\AgdaSpace{}%
\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,}}\AgdaSpace{}%
\AgdaBound{y}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∣}}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{x}\<%
\\
%
\>[1]\AgdaFunction{fst}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,}}\AgdaSpace{}%
\AgdaBound{y}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{x}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
%
\>[1]\AgdaOperator{\AgdaFunction{∥\AgdaUnderscore{}∥}}\AgdaSpace{}%
\AgdaFunction{snd}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{X}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{𝓤}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{̇}}\AgdaSpace{}%
\AgdaSymbol{\}\{}\AgdaBound{Y}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{X}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaGeneralizable{𝓥}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{̇}}\AgdaSpace{}%
\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{z}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaRecord{Σ}\AgdaSpace{}%
\AgdaBound{Y}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaBound{Y}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{pr₁}\AgdaSpace{}%
\AgdaBound{z}\AgdaSymbol{)}\<%
\\
%
\>[1]\AgdaOperator{\AgdaFunction{∥}}\AgdaSpace{}%
\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,}}\AgdaSpace{}%
\AgdaBound{y}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∥}}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{y}\<%
\\
%
\>[1]\AgdaFunction{snd}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,}}\AgdaSpace{}%
\AgdaBound{y}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{y}\<%
\\
\>[0]\<%
\end{code}

For the dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing (and more standard in the literature) than Agda's default syntax (`Σ λ(x ꞉ X) → y`). The preferred notation is made available by making the index type explicit.

```agda
infixr -1 -Σ
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
syntax -Σ X (λ x → y) = Σ x ꞉ X , y -- type `꞉` as `\:4`
```

<div class="admonition warning">

The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

</div>

MHE explains Sigma induction as follows: "To prove that `A z` holds for all `z : Σ Y`, for a given property `A`, we just prove that we have `A (x , y)` for all `x : X` and `y : Y x`. This is called `Σ` induction or `Σ` elimination (or `uncurry`).

```agda
Σ-induction : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
 →            ((x : X)(y : Y x) → A (x , y))
              -------------------------------
 →            ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ }{A : Σ Y → 𝓦 ̇ }
 →      (((x , y) : Σ Y ) → A (x , y))
       ---------------------------------
 →      ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)
```

The special case in which the type `Y` doesn't depend on `X` is the usual Cartesian product.

```agda
infixr 30 _×_
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y
```

------------------

#### <a id="dependent-function-type">Dependent function type</a>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), MHE uses the same trick as the one used above for *Sigma types*.

```agda
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe}(X : 𝓤 ̇ )(Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y
infixr -1 -Π
syntax -Π A (λ x → b) = Π x ꞉ A , b
```

---------------------------------------------------

#### <a id="truncation">Truncation</a>

In general, we may have many inhabitants of a given type and, via the Curry-Howard correspondence, many proofs of a given proposition.  For instance, suppose we have a type `X` and an identity relation ≡ₓ on X. Then, given two inhabitants `a` and `b` of type `X`, we may ask whether `a ≡ₓ b`.

Suppose `p` and `q` inhabit the identity type `a ≡ₓ b`; that is, `p` and `q` are proofs of `a ≡ₓ b`, in which case we write `p  q : a ≡ₓ b`.  Then we might wonder whether and in what sense are the two proofs `p` and `q` the "same."  We are asking about an identity type on the identity type ≡ₓ, and whether there is some inhabitant `r` of this type; i.e., whether there is a proof `r : p ≡ₓ₁ q` that the proof of `a ≡ₓ b` is unique.  (This property is sometimes called *uniqueness of identity proofs*.)

Perhaps we have two proofs, say, `r s : p ≡ₓ₁ q`. Then of course we will ask whether `r ≡ₓ₂ s` has a proof!  But at some level we may decide that the potential to distinguish two proofs of an identity in a meaningful way (so-called *proof relevance*) is not useful or desirable.  At that point, say, at level `k`, we might assume that there is at most one proof of any identity of the form `p ≡ₓₖ q`.  This is called [truncation](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation).

We will see some examples of trunction later when we require it to complete some of the UALib modules leading up to the proof of Birkhoff's HSP Theorem.  Readers who want more details should refer to [Section 34](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) and [35](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing) of MHE's notes, or [Guillaume Brunerie, Truncations and truncated higher inductive types](https://homotopytypetheory.org/2012/09/16/truncations-and-truncated-higher-inductive-types/), or Section 7.1 of the [HoTT book][].

We take this opportunity to define *set* (or 0-*groupoid*) in type theory.  A type X : 𝓤 ̇ with an identity relation `≡ₓ` is called a **set** if for every pair `a b : X` of elements of type `X` there is at most one proof of `a ≡ₓ b`.

This notion is formalized in the [Type Topology][] library as follows:<span class="footnote"><sup>2</sup></span>

```agda
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
```

----------------------------------------

<span class="footnote"><sup>1</sup> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<br></br>

<span class="footnote"><sup>2</sup>As [MHE][] explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."</span>

<p></p>

[↑ UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Prelude.Equality →](UALib.Prelude.Equality.html)</span>


{% include UALib.Links.md %}

