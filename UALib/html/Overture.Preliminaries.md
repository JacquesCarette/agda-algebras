---
layout: default
title : Overture.Preliminaries module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

<!--
FILE: Preliminaries.lagda
AUTHOR: William DeMeo
DATE: 14 Jan 2021
REF: Parts of this file are based on the HoTT/UF course notes by Martín Hötzel Escardó.
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
-->

### <a id="preliminaries">Preliminaries</a>

This is the [Overture.Preliminaries][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

The [Agda UALib][] is based on a type theory that is the same or very close to the one on which on which Martín Escardó's [Type Topology][] Agda library is based. We don't discuss [MLTT][] in great detail here because there are already nice and freely available resources covering the theory. (See, for example, the section of [Escardó's notes][] on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda), the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), or the [HoTT Book][].)

The objects and assumptions that form the foundation of [MLTT][] are few.  There are the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type). Each of these type formers is defined by a *type forming rule* which specifies how that type is constructed. Lastly, we have an infinite collection of *type universes* (types of types) and *universe variables* to denote them. Following Escardó, use denote universes in the [UALib][] by upper-case calligraphic letters from the second half of the English alphabet; to be precise, these are `𝓞`, `𝓠`, `𝓡`, …, `𝓧`, `𝓨`, `𝓩`.<sup>[0](Overture.Preliminaries.html#fn0)</sup>

That's all. There are no further axioms or logical deduction (proof derivation) rules needed for the foundation of [MLTT][] that we take as the starting point of the [Agda UALib][].  The logical semantics come from the [propositions-as-types correspondence](https://ncatlab.org/nlab/show/propositions+as+types): propositions and predicates are represented by types and the inhabitants of these types are the proofs of the propositions and predicates.  As such, proofs are constructed using the type forming rules. In other words, the type forming rules *are* the proof derivation rules.

To this foundation, we add certain *extensionality principles* when and were we need them.  These will be developed as we progress.  However, classical axioms such as the [*Axiom of Choice*](https://ncatlab.org/nlab/show/axiom+of+choice) or the [*Law of the Excluded Middle*](https://ncatlab.org/nlab/show/excluded+middle) are not needed and are not assumed anywhere in the library.  In this sense, all theorems and proofs in the [UALib][] are [*constructive*](https://ncatlab.org/nlab/show/constructive+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/constructive+mathematics)).

A few specific instances (e.g., the proof of the Noether isomorphism theorems and Birkhoff's HSP theorem) require certain *truncation* assumptions. In such cases, the theory is not [predicative](https://ncatlab.org/nlab/show/predicative+mathematics) (according to [nlab's definition](https://ncatlab.org/nlab/show/predicative+mathematics)). These instances are always clearly identified.



#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="4064" class="Symbol">{-#</a> <a id="4068" class="Keyword">OPTIONS</a> <a id="4076" class="Pragma">--without-K</a> <a id="4088" class="Pragma">--exact-split</a> <a id="4102" class="Pragma">--safe</a> <a id="4109" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Overture.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="5822" class="Keyword">module</a> <a id="5829" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a> <a id="5852" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




#### <a id="agda-universes">Agda Universes</a>

For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.<sup>[1](Overture.Preliminaries.html#fn1)</sup>  The first of these is the `Universes` module which we import here.<sup>[2](Overture.Preliminaries.html#fn2)</sup>

<pre class="Agda">

<a id="7662" class="Keyword">open</a> <a id="7667" class="Keyword">import</a> <a id="7674" href="Universes.html" class="Module">Universes</a> <a id="7684" class="Keyword">public</a>

</pre>

Since we use the `public` directive, the `Universes` module will be available to all modules that import the present module ([Overture.Preliminaries][]). This module declares symbols used to denote universes.  As mentioned, we adopt Escardó's convention of denoting universes by capital calligraphic letters, and most of the ones we use are already declared in the `Universes` module; those that are not are declared as follows.

<pre class="Agda">

<a id="8148" class="Keyword">variable</a> <a id="8157" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="8159" href="Overture.Preliminaries.html#8159" class="Generalizable">𝓧</a> <a id="8161" href="Overture.Preliminaries.html#8161" class="Generalizable">𝓨</a> <a id="8163" href="Overture.Preliminaries.html#8163" class="Generalizable">𝓩</a> <a id="8165" class="Symbol">:</a> <a id="8167" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

The `Universes` module also provides alternative syntax for the primitive operations on universes that Agda supports.  The ` ̇` operator maps a universe level `𝓤` to the type `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`. The primitive Agda level `lzero` is renamed `𝓤₀`, so `𝓤₀ ̇` is an alias for `Set lzero`. Thus, `𝓤 ̇` is simply an alias for `Set 𝓤`, and we have the typing judgment `Set 𝓤 : Set (lsuc 𝓤)`. Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we (and [Escardó][]) denote by `𝓤₀ ⁺ ̇`.

The following dictionary translates between standard Agda syntax and Type Topology/UALib notation.

```agda
Agda              Type Topology/UALib
====              ===================
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

To justify the introduction of this somewhat nonstandard notation for universe levels, [Escardó][] points out that the Agda library uses `Level` for universes (so what we write as `𝓤 ̇` is written `Set 𝓤` in standard Agda), but in univalent mathematics the types in `𝓤 ̇` need not be sets, so the standard Agda notation can be misleading.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, `𝓤 ̇` and `𝓥 ̇` . The universe `𝓤 ⊔ 𝓥 ̇` denotes this least upper bound. Here `𝓤 ⊔ 𝓥̇ ` is used to denote the universe level corresponding to the least upper bound of the levels `𝓤` and `𝓥`, where the `_⊔_` is an Agda primitive designed for precisely this purpose.


#### <a id="dependent-pair-type">Sigma types (dependent pairs)</a>

Given universes 𝓤 and 𝓥, a type `A : 𝓤 ̇`, and a type family `B : A → 𝓥 ̇`, the *Sigma type* (or *dependent pair type*), denoted by `Σ(x ꞉ A), B x`, generalizes the Cartesian product `A × B` by allowing the type `B x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, an inhabitant of the type `Σ(x ꞉ A), B x` is a pair `(x , y)` such that `x : A` and `y : B x`.

The [Type Topology][] library contains a standard definition of the dependent product.
For pedagogical purposes we repeat this definition here, inside a *hidden module* so that it doesn't conflict with the original definition that we import later.<sup>[3](Overture.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="10653" class="Keyword">module</a> <a id="hide-sigma"></a><a id="10660" href="Overture.Preliminaries.html#10660" class="Module">hide-sigma</a> <a id="10671" class="Keyword">where</a>

 <a id="10679" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="10686" href="Overture.Preliminaries.html#10686" class="Record">Σ</a> <a id="10688" class="Symbol">{</a><a id="10689" href="Overture.Preliminaries.html#10689" class="Bound">𝓤</a> <a id="10691" href="Overture.Preliminaries.html#10691" class="Bound">𝓥</a><a id="10692" class="Symbol">}</a> <a id="10694" class="Symbol">{</a><a id="10695" href="Overture.Preliminaries.html#10695" class="Bound">A</a> <a id="10697" class="Symbol">:</a> <a id="10699" href="Overture.Preliminaries.html#10689" class="Bound">𝓤</a> <a id="10701" href="Universes.html#403" class="Function Operator">̇</a> <a id="10703" class="Symbol">}</a> <a id="10705" class="Symbol">(</a><a id="10706" href="Overture.Preliminaries.html#10706" class="Bound">B</a> <a id="10708" class="Symbol">:</a> <a id="10710" href="Overture.Preliminaries.html#10695" class="Bound">A</a> <a id="10712" class="Symbol">→</a> <a id="10714" href="Overture.Preliminaries.html#10691" class="Bound">𝓥</a> <a id="10716" href="Universes.html#403" class="Function Operator">̇</a> <a id="10718" class="Symbol">)</a> <a id="10720" class="Symbol">:</a> <a id="10722" href="Overture.Preliminaries.html#10689" class="Bound">𝓤</a> <a id="10724" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10726" href="Overture.Preliminaries.html#10691" class="Bound">𝓥</a> <a id="10728" href="Universes.html#403" class="Function Operator">̇</a>  <a id="10731" class="Keyword">where</a>
  <a id="10739" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="10751" href="Overture.Preliminaries.html#10751" class="InductiveConstructor Operator">_,_</a>
  <a id="10757" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="10766" href="Overture.Preliminaries.html#10766" class="Field">pr₁</a> <a id="10770" class="Symbol">:</a> <a id="10772" href="Overture.Preliminaries.html#10695" class="Bound">A</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="10777" href="Overture.Preliminaries.html#10777" class="Field">pr₂</a> <a id="10781" class="Symbol">:</a> <a id="10783" href="Overture.Preliminaries.html#10706" class="Bound">B</a> <a id="10785" href="Overture.Preliminaries.html#10766" class="Field">pr₁</a>

 <a id="10791" class="Keyword">infixr</a> <a id="10798" class="Number">50</a> <a id="10801" href="Overture.Preliminaries.html#10751" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ A , B`, which is more pleasing and more standard than Agda's default syntax, `Σ A (λ x → B)`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="11121" href="Overture.Preliminaries.html#11121" class="Function">-Σ</a> <a id="11124" class="Symbol">:</a> <a id="11126" class="Symbol">{</a><a id="11127" href="Overture.Preliminaries.html#11127" class="Bound">𝓤</a> <a id="11129" href="Overture.Preliminaries.html#11129" class="Bound">𝓥</a> <a id="11131" class="Symbol">:</a> <a id="11133" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="11141" class="Symbol">}</a> <a id="11143" class="Symbol">(</a><a id="11144" href="Overture.Preliminaries.html#11144" class="Bound">A</a> <a id="11146" class="Symbol">:</a> <a id="11148" href="Overture.Preliminaries.html#11127" class="Bound">𝓤</a> <a id="11150" href="Universes.html#403" class="Function Operator">̇</a> <a id="11152" class="Symbol">)</a> <a id="11154" class="Symbol">(</a><a id="11155" href="Overture.Preliminaries.html#11155" class="Bound">B</a> <a id="11157" class="Symbol">:</a> <a id="11159" href="Overture.Preliminaries.html#11144" class="Bound">A</a> <a id="11161" class="Symbol">→</a> <a id="11163" href="Overture.Preliminaries.html#11129" class="Bound">𝓥</a> <a id="11165" href="Universes.html#403" class="Function Operator">̇</a> <a id="11167" class="Symbol">)</a> <a id="11169" class="Symbol">→</a> <a id="11171" href="Overture.Preliminaries.html#11127" class="Bound">𝓤</a> <a id="11173" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11175" href="Overture.Preliminaries.html#11129" class="Bound">𝓥</a> <a id="11177" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11180" href="Overture.Preliminaries.html#11121" class="Function">-Σ</a> <a id="11183" href="Overture.Preliminaries.html#11183" class="Bound">A</a> <a id="11185" href="Overture.Preliminaries.html#11185" class="Bound">B</a> <a id="11187" class="Symbol">=</a> <a id="11189" href="Overture.Preliminaries.html#10686" class="Record">Σ</a> <a id="11191" href="Overture.Preliminaries.html#11185" class="Bound">B</a>

 <a id="11195" class="Keyword">syntax</a> <a id="11202" href="Overture.Preliminaries.html#11121" class="Function">-Σ</a> <a id="11205" class="Bound">A</a> <a id="11207" class="Symbol">(λ</a> <a id="11210" class="Bound">x</a> <a id="11212" class="Symbol">→</a> <a id="11214" class="Bound">B</a><a id="11215" class="Symbol">)</a> <a id="11217" class="Symbol">=</a> <a id="11219" class="Function">Σ</a> <a id="11221" class="Bound">x</a> <a id="11223" class="Function">꞉</a> <a id="11225" class="Bound">A</a> <a id="11227" class="Function">,</a> <a id="11229" class="Bound">B</a>

</pre>

**Warning!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ A , B` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `B` doesn't depend on `A`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="11602" href="Overture.Preliminaries.html#11602" class="Function Operator">_×_</a> <a id="11606" class="Symbol">:</a> <a id="11608" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="11610" href="Universes.html#403" class="Function Operator">̇</a> <a id="11612" class="Symbol">→</a> <a id="11614" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="11616" href="Universes.html#403" class="Function Operator">̇</a> <a id="11618" class="Symbol">→</a> <a id="11620" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="11622" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11624" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="11626" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11629" href="Overture.Preliminaries.html#11629" class="Bound">A</a> <a id="11631" href="Overture.Preliminaries.html#11602" class="Function Operator">×</a> <a id="11633" href="Overture.Preliminaries.html#11633" class="Bound">B</a> <a id="11635" class="Symbol">=</a> <a id="11637" href="Overture.Preliminaries.html#11121" class="Function">Σ</a> <a id="11639" href="Overture.Preliminaries.html#11639" class="Bound">x</a> <a id="11641" href="Overture.Preliminaries.html#11121" class="Function">꞉</a> <a id="11643" href="Overture.Preliminaries.html#11629" class="Bound">A</a> <a id="11645" href="Overture.Preliminaries.html#11121" class="Function">,</a> <a id="11647" href="Overture.Preliminaries.html#11633" class="Bound">B</a>

</pre>


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).

<pre class="Agda">

<a id="12202" class="Keyword">module</a> <a id="hide-pi"></a><a id="12209" href="Overture.Preliminaries.html#12209" class="Module">hide-pi</a> <a id="12217" class="Symbol">{</a><a id="12218" href="Overture.Preliminaries.html#12218" class="Bound">𝓤</a> <a id="12220" href="Overture.Preliminaries.html#12220" class="Bound">𝓦</a> <a id="12222" class="Symbol">:</a> <a id="12224" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12232" class="Symbol">}</a> <a id="12234" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="12242" href="Overture.Preliminaries.html#12242" class="Function">Π</a> <a id="12244" class="Symbol">:</a> <a id="12246" class="Symbol">{</a><a id="12247" href="Overture.Preliminaries.html#12247" class="Bound">A</a> <a id="12249" class="Symbol">:</a> <a id="12251" href="Overture.Preliminaries.html#12218" class="Bound">𝓤</a> <a id="12253" href="Universes.html#403" class="Function Operator">̇</a> <a id="12255" class="Symbol">}</a> <a id="12257" class="Symbol">(</a><a id="12258" href="Overture.Preliminaries.html#12258" class="Bound">B</a> <a id="12260" class="Symbol">:</a> <a id="12262" href="Overture.Preliminaries.html#12247" class="Bound">A</a> <a id="12264" class="Symbol">→</a> <a id="12266" href="Overture.Preliminaries.html#12220" class="Bound">𝓦</a> <a id="12268" href="Universes.html#403" class="Function Operator">̇</a> <a id="12270" class="Symbol">)</a> <a id="12272" class="Symbol">→</a> <a id="12274" href="Overture.Preliminaries.html#12218" class="Bound">𝓤</a> <a id="12276" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12278" href="Overture.Preliminaries.html#12220" class="Bound">𝓦</a> <a id="12280" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12283" href="Overture.Preliminaries.html#12242" class="Function">Π</a> <a id="12285" class="Symbol">{</a><a id="12286" href="Overture.Preliminaries.html#12286" class="Bound">A</a><a id="12287" class="Symbol">}</a> <a id="12289" href="Overture.Preliminaries.html#12289" class="Bound">B</a> <a id="12291" class="Symbol">=</a> <a id="12293" class="Symbol">(</a><a id="12294" href="Overture.Preliminaries.html#12294" class="Bound">x</a> <a id="12296" class="Symbol">:</a> <a id="12298" href="Overture.Preliminaries.html#12286" class="Bound">A</a><a id="12299" class="Symbol">)</a> <a id="12301" class="Symbol">→</a> <a id="12303" href="Overture.Preliminaries.html#12289" class="Bound">B</a> <a id="12305" href="Overture.Preliminaries.html#12294" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="12309" href="Overture.Preliminaries.html#12309" class="Function">-Π</a> <a id="12312" class="Symbol">:</a> <a id="12314" class="Symbol">(</a><a id="12315" href="Overture.Preliminaries.html#12315" class="Bound">A</a> <a id="12317" class="Symbol">:</a> <a id="12319" href="Overture.Preliminaries.html#12218" class="Bound">𝓤</a> <a id="12321" href="Universes.html#403" class="Function Operator">̇</a> <a id="12323" class="Symbol">)(</a><a id="12325" href="Overture.Preliminaries.html#12325" class="Bound">B</a> <a id="12327" class="Symbol">:</a> <a id="12329" href="Overture.Preliminaries.html#12315" class="Bound">A</a> <a id="12331" class="Symbol">→</a> <a id="12333" href="Overture.Preliminaries.html#12220" class="Bound">𝓦</a> <a id="12335" href="Universes.html#403" class="Function Operator">̇</a> <a id="12337" class="Symbol">)</a> <a id="12339" class="Symbol">→</a> <a id="12341" href="Overture.Preliminaries.html#12218" class="Bound">𝓤</a> <a id="12343" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="12345" href="Overture.Preliminaries.html#12220" class="Bound">𝓦</a> <a id="12347" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="12350" href="Overture.Preliminaries.html#12309" class="Function">-Π</a> <a id="12353" href="Overture.Preliminaries.html#12353" class="Bound">A</a> <a id="12355" href="Overture.Preliminaries.html#12355" class="Bound">B</a> <a id="12357" class="Symbol">=</a> <a id="12359" href="Overture.Preliminaries.html#12242" class="Function">Π</a> <a id="12361" href="Overture.Preliminaries.html#12355" class="Bound">B</a>

 <a id="12365" class="Keyword">infixr</a> <a id="12372" class="Number">-1</a> <a id="12375" href="Overture.Preliminaries.html#12309" class="Function">-Π</a>
 <a id="12379" class="Keyword">syntax</a> <a id="12386" href="Overture.Preliminaries.html#12309" class="Function">-Π</a> <a id="12389" class="Bound">A</a> <a id="12391" class="Symbol">(λ</a> <a id="12394" class="Bound">x</a> <a id="12396" class="Symbol">→</a> <a id="12398" class="Bound">B</a><a id="12399" class="Symbol">)</a> <a id="12401" class="Symbol">=</a> <a id="12403" class="Function">Π</a> <a id="12405" class="Bound">x</a> <a id="12407" class="Function">꞉</a> <a id="12409" class="Bound">A</a> <a id="12411" class="Function">,</a> <a id="12413" class="Bound">B</a>

</pre>

**Warning!** The symbol ꞉ is not the same as :. Type the colon in `Π x ꞉ A , B` as `\:4` in [agda2-mode][].

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Overture.Preliminaries][].

<pre class="Agda">

<a id="13013" class="Keyword">open</a> <a id="13018" class="Keyword">import</a> <a id="13025" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="13036" class="Keyword">renaming</a> <a id="13045" class="Symbol">(</a><a id="13046" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="13050" class="Symbol">to</a> <a id="13053" class="Keyword">infixr</a> <a id="13060" class="Number">50</a> <a id="_,_"></a><a id="13063" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">_,_</a><a id="13066" class="Symbol">)</a> <a id="13068" class="Keyword">public</a>
<a id="13075" class="Keyword">open</a> <a id="13080" class="Keyword">import</a> <a id="13087" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="13096" class="Keyword">using</a> <a id="13102" class="Symbol">(</a><a id="13103" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="13106" class="Symbol">;</a> <a id="13108" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="13111" class="Symbol">;</a> <a id="13113" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="13116" class="Symbol">;</a> <a id="13118" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="13120" class="Symbol">;</a> <a id="13122" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="13123" class="Symbol">;</a> <a id="13125" href="MGS-MLTT.html#3635" class="Function">-Π</a><a id="13127" class="Symbol">)</a> <a id="13129" class="Keyword">public</a>

</pre>

#### <a id="projection notation">Projection notation</a>

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣_∣` and `∥_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.


<pre class="Agda">

<a id="13704" class="Keyword">module</a> <a id="13711" href="Overture.Preliminaries.html#13711" class="Module">_</a> <a id="13713" class="Symbol">{</a><a id="13714" href="Overture.Preliminaries.html#13714" class="Bound">𝓤</a> <a id="13716" class="Symbol">:</a> <a id="13718" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="13726" class="Symbol">}{</a><a id="13728" href="Overture.Preliminaries.html#13728" class="Bound">A</a> <a id="13730" class="Symbol">:</a> <a id="13732" href="Overture.Preliminaries.html#13714" class="Bound">𝓤</a> <a id="13734" href="Universes.html#403" class="Function Operator">̇</a> <a id="13736" class="Symbol">}{</a><a id="13738" href="Overture.Preliminaries.html#13738" class="Bound">B</a> <a id="13740" class="Symbol">:</a> <a id="13742" href="Overture.Preliminaries.html#13728" class="Bound">A</a> <a id="13744" class="Symbol">→</a> <a id="13746" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="13748" href="Universes.html#403" class="Function Operator">̇</a><a id="13749" class="Symbol">}</a> <a id="13751" class="Keyword">where</a>

 <a id="13759" href="Overture.Preliminaries.html#13759" class="Function Operator">∣_∣</a> <a id="13763" href="Overture.Preliminaries.html#13763" class="Function">fst</a> <a id="13767" class="Symbol">:</a> <a id="13769" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13771" href="Overture.Preliminaries.html#13738" class="Bound">B</a> <a id="13773" class="Symbol">→</a> <a id="13775" href="Overture.Preliminaries.html#13728" class="Bound">A</a>
 <a id="13778" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="13780" href="Overture.Preliminaries.html#13780" class="Bound">x</a> <a id="13782" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">,</a> <a id="13784" href="Overture.Preliminaries.html#13784" class="Bound">y</a> <a id="13786" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="13788" class="Symbol">=</a> <a id="13790" href="Overture.Preliminaries.html#13780" class="Bound">x</a>
 <a id="13793" href="Overture.Preliminaries.html#13763" class="Function">fst</a> <a id="13797" class="Symbol">(</a><a id="13798" href="Overture.Preliminaries.html#13798" class="Bound">x</a> <a id="13800" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">,</a> <a id="13802" href="Overture.Preliminaries.html#13802" class="Bound">y</a><a id="13803" class="Symbol">)</a> <a id="13805" class="Symbol">=</a> <a id="13807" href="Overture.Preliminaries.html#13798" class="Bound">x</a>

 <a id="13811" href="Overture.Preliminaries.html#13811" class="Function Operator">∥_∥</a> <a id="13815" href="Overture.Preliminaries.html#13815" class="Function">snd</a> <a id="13819" class="Symbol">:</a> <a id="13821" class="Symbol">(</a><a id="13822" href="Overture.Preliminaries.html#13822" class="Bound">z</a> <a id="13824" class="Symbol">:</a> <a id="13826" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="13828" href="Overture.Preliminaries.html#13738" class="Bound">B</a><a id="13829" class="Symbol">)</a> <a id="13831" class="Symbol">→</a> <a id="13833" href="Overture.Preliminaries.html#13738" class="Bound">B</a> <a id="13835" class="Symbol">(</a><a id="13836" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="13840" href="Overture.Preliminaries.html#13822" class="Bound">z</a><a id="13841" class="Symbol">)</a>
 <a id="13844" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="13846" href="Overture.Preliminaries.html#13846" class="Bound">x</a> <a id="13848" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">,</a> <a id="13850" href="Overture.Preliminaries.html#13850" class="Bound">y</a> <a id="13852" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="13854" class="Symbol">=</a> <a id="13856" href="Overture.Preliminaries.html#13850" class="Bound">y</a>
 <a id="13859" href="Overture.Preliminaries.html#13815" class="Function">snd</a> <a id="13863" class="Symbol">(</a><a id="13864" href="Overture.Preliminaries.html#13864" class="Bound">x</a> <a id="13866" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">,</a> <a id="13868" href="Overture.Preliminaries.html#13868" class="Bound">y</a><a id="13869" class="Symbol">)</a> <a id="13871" class="Symbol">=</a> <a id="13873" href="Overture.Preliminaries.html#13868" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.

Also note that multiple inhabitants of a single type (e.g., `∣_∣` and `fst`) may be declared on the same line.

----------------------------------------

<sup>0</sup><span class="footnote" id="fn0"> We avoid using `𝓟` as a universe variable because in the [Type Topology][] library `𝓟` denotes a powerset type.</span>

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes entitled [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html) which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.</span>

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3">To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library as long as we don't invoke `open hide-refl`. It may seem odd to define something in a hidden module only to import and use an alternative definition, but we do so in order to exhibit all of the types on which the [UALib][] depends while ensuring that this is not misinterpreted as a claim to originality.</span>

<br>
<br>

[↑ Overture](Overture.html)
<span style="float:right;">[Overture.Equality →](Overture.Equality.html)</span>


{% include UALib.Links.md %}

<!--

<sup>3</sup><span class="footnote" id="fn3">We have made a concerted effort to avoid duplicating types that are already provided elsewhere, such as the [Type Topology][] library.  We occasionally repeat the definitions of such types for pedagogical purposes, but we almost always import and work with the original definitions in order to make the sources known and to credit the original authors.</span>



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

Actually, for illustration purposes, the example we gave here is not one that Agda would normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope. We tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.
-->
