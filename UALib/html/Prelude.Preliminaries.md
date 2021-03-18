---
layout: default
title : Prelude.Preliminaries module (The Agda Universal Algebra Library)
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

This is the [Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

#### <a id="logical-foundations">Logical foundations</a>

For the benefit of readers who are not proficient in Agda or type theory, we briefly describe some of the type theoretic foundations of the [Agda UALib][], as well as the most important basic types and features that are used throughout the library.

The [UALib][] is based on a minimal version of [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory) (MLTT) which is the same or very close to the type theory on which Martin Escardo's [Type Topology][] Agda library is based.  We won't go into great detail here because there are already other very nice resources available, such as the section on [A spartan Martin-Löf type theory](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html\#mlttinagda) of the lecture notes by Escardó just mentioned, the [ncatlab entry on Martin-Löf dependent type theory](https://ncatlab.org/nlab/show/Martin-L\%C3\%B6f+dependent+type+theory), and the [HoTT Book][].

We begin by noting that only a very small collection of objects is assumed at the jumping-off point for MLTT. We have the *primitive types* (`𝟘`, `𝟙`, and `ℕ`, denoting the empty type, one-element type, and natural numbers), the *type formers* (`+`, `Π`, `Σ`, `Id`, denoting *binary sum*, *product*, *sum*, and the *identity* type), and an infinite collection of *type universes* (types of types) and universe variables to denote them.
Like Escardó's, our universe variables are typically upper-case caligraphic letters from the latter half of the English alphabet (e.g., `𝓤`, `𝓥`, `𝓦`, etc.).


#### <a id="specifying-logical-foundations">Specifying logical foundations in Agda</a>

An Agda program typically begins by setting some options and by importing types from existing Agda libraries.
Options are specified with the `OPTIONS` *pragma* and control the way Agda behaves by, for example, specifying the logical axioms and deduction rules we wish to assume when the program is type-checked to verify its correctness. Every Agda program in the [UALib][] begins with the following line.

<pre class="Agda">

<a id="2634" class="Symbol">{-#</a> <a id="2638" class="Keyword">OPTIONS</a> <a id="2646" class="Pragma">--without-K</a> <a id="2658" class="Pragma">--exact-split</a> <a id="2672" class="Pragma">--safe</a> <a id="2679" class="Symbol">#-}</a>

</pre>

These options control certain foundational assumptions that Agda makes when type-checking the program to verify its correctness.

* `--without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

* `--exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* equalities.  [Escardó][] explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

* `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must replace the `--safe` flag with `--allow-unsolved-metas`, but this is never done in (publicly released versions of) the [UALib][].



#### <a id="agda-modules">Agda Modules</a>

The `OPTIONS` pragma is usually followed by the start of a module.  For example, the [Prelude.Preliminaries][] module begins with the following line.

<pre class="Agda">

<a id="4391" class="Keyword">module</a> <a id="4398" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="4420" class="Keyword">where</a>

</pre>

Sometimes we want to declare parameters that will be assumed throughout the module.  For instance, when working with algebras, we often assume they come from a particular fixed signature, and this signature is something we could fix as a parameter at the start of a module. Thus we might start an *anonymous submodule* of the main module with a line like `module _ {𝑆 : Signature 𝓞 𝓥} where`.  Such a module is called *anonymous* because an underscore `_` appears in place of a module name. Agda determines where the submodule ends by indentation.  This can take some getting used to, but after a short time it will feel very natural.

The main module of a file must have the same name as the file, without the `.agda` or `.lagda` file extension.  The code inside the main module is not indented. Submodules are declared inside the main module and code inside these submodules must be indented to a fixed column.  As long as the code is indented, Agda considers it part of the submodule.  A submodule is exited as soon as a nonindented line of code appears.




#### <a id="Universes">Universes</a>

For the very small amount of background about *type universes* we require, we refer the reader to the brief [section on universe-levels](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html) in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.1.3/language/universe-levels.html).

Throughout we use many of the nice tools that [Martín Escardó][] has developed and made available in the [Type Topology][] repository of Agda code for the *Univalent Foundations* of mathematics.<sup>[1](Prelude.Preliminaries.html#fn1)</sup>  The first of these is the `Universes` module which we import here.<sup>[2](Prelude.Preliminaries.html#fn2)</sup>

<pre class="Agda">

<a id="6218" class="Keyword">open</a> <a id="6223" class="Keyword">import</a> <a id="6230" href="Universes.html" class="Module">Universes</a> <a id="6240" class="Keyword">public</a>

</pre>

Since we used the `public` directive, the `Universes` module will be available to all modules that import [Prelude.Preliminaries][].

The `Universes` module includes a number of symbols used to denote *universes* in Agda. We add one more to the list that we will use to denote the universe level of operation symbol types (defined in the [Algebras.Signatures][] module).

<pre class="Agda">

<a id="6646" class="Keyword">variable</a>
 <a id="6656" href="Prelude.Preliminaries.html#6656" class="Generalizable">𝓞</a> <a id="6658" class="Symbol">:</a> <a id="6660" href="Agda.Primitive.html#423" class="Postulate">Universe</a>

</pre>

The `Universes` module also provides an elegant notation for type universes, and we adopt this notation throughout the Agda UALib.

Following [Escardó][], we refer to universes using capitalized script letters from near the end of the alphabet, e.g., 𝓤, 𝓥, 𝓦, 𝓧, 𝓨, 𝓩, etc.

Also in the `Universes` module [Escardó][] defines the ̇ operator which maps a universe 𝓤 (i.e., a level) to `Set 𝓤`, and the latter has type `Set (lsuc 𝓤)`.

The level `lzero` is renamed 𝓤₀, so 𝓤₀ ̇ is an alias for `Set lzero` (which, incidentally, corresponds to `Sort 0` in the [Lean][] proof assistant language).

Thus, 𝓤 ̇ is simply an alias for `Set 𝓤`, and we have `Set 𝓤 : Set (lsuc 𝓤)`.

Finally, `Set (lsuc lzero)` is denoted by `Set 𝓤₀ ⁺` which we (and [Escardó][]) denote by `𝓤₀ ⁺ ̇`.

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

To justify the introduction of this somewhat nonstandard notation for universe levels, [Escardó][] points out that the Agda library uses `Level` for universes (so what we write as 𝓤 ̇ is written `Set 𝓤` in standard Agda), but in univalent mathematics the types in 𝓤 ̇ need not be sets, so the standard Agda notation can be misleading.

There will be many occasions calling for a type living in the universe that is the least upper bound of two universes, say, 𝓤 ̇ and 𝓥 ̇ . The universe 𝓤 ⊔ 𝓥 ̇ denotes this least upper bound. Here 𝓤 ⊔ 𝓥 is used to denote the universe level corresponding to the least upper bound of the levels 𝓤 and 𝓥, where the `_⊔_` is an Agda primitive designed for precisely this purpose.


#### <a id="dependent-pair-type">Sigma types (dependent pairs)</a>

Given universes 𝓤 and 𝓥, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the **Sigma type** (or **dependent pair type**), denoted by `Σ(x ꞉ X), Y x`, generalizes the Cartesian product `X × Y` by allowing the type `Y x` of the second argument of the ordered pair `(x , y)` to depend on the value `x` of the first.  That is, an inhabitant of the type `Σ(x ꞉ X), Y x` is a pair `(x , y)` such that `x : X` and `y : Y x`.

The [Type Topology][] library contains a standard definition of the dependent product.
For pedagogical purposes we repeat this definition here, inside a *hidden module* so that it doesn't conflict with the original definition that we import later.<sup>[3](Prelude.Equality.html#fn3)</sup>

<pre class="Agda">

<a id="9390" class="Keyword">module</a> <a id="hide-sigma"></a><a id="9397" href="Prelude.Preliminaries.html#9397" class="Module">hide-sigma</a> <a id="9408" class="Keyword">where</a>

 <a id="9416" class="Keyword">record</a> <a id="hide-sigma.Σ"></a><a id="9423" href="Prelude.Preliminaries.html#9423" class="Record">Σ</a> <a id="9425" class="Symbol">{</a><a id="9426" href="Prelude.Preliminaries.html#9426" class="Bound">𝓤</a> <a id="9428" href="Prelude.Preliminaries.html#9428" class="Bound">𝓥</a><a id="9429" class="Symbol">}</a> <a id="9431" class="Symbol">{</a><a id="9432" href="Prelude.Preliminaries.html#9432" class="Bound">X</a> <a id="9434" class="Symbol">:</a> <a id="9436" href="Prelude.Preliminaries.html#9426" class="Bound">𝓤</a> <a id="9438" href="Universes.html#403" class="Function Operator">̇</a> <a id="9440" class="Symbol">}</a> <a id="9442" class="Symbol">(</a><a id="9443" href="Prelude.Preliminaries.html#9443" class="Bound">Y</a> <a id="9445" class="Symbol">:</a> <a id="9447" href="Prelude.Preliminaries.html#9432" class="Bound">X</a> <a id="9449" class="Symbol">→</a> <a id="9451" href="Prelude.Preliminaries.html#9428" class="Bound">𝓥</a> <a id="9453" href="Universes.html#403" class="Function Operator">̇</a> <a id="9455" class="Symbol">)</a> <a id="9457" class="Symbol">:</a> <a id="9459" href="Prelude.Preliminaries.html#9426" class="Bound">𝓤</a> <a id="9461" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9463" href="Prelude.Preliminaries.html#9428" class="Bound">𝓥</a> <a id="9465" href="Universes.html#403" class="Function Operator">̇</a>  <a id="9468" class="Keyword">where</a>
  <a id="9476" class="Keyword">constructor</a> <a id="hide-sigma._,_"></a><a id="9488" href="Prelude.Preliminaries.html#9488" class="InductiveConstructor Operator">_,_</a>
  <a id="9494" class="Keyword">field</a>
   <a id="hide-sigma.Σ.pr₁"></a><a id="9503" href="Prelude.Preliminaries.html#9503" class="Field">pr₁</a> <a id="9507" class="Symbol">:</a> <a id="9509" href="Prelude.Preliminaries.html#9432" class="Bound">X</a>
   <a id="hide-sigma.Σ.pr₂"></a><a id="9514" href="Prelude.Preliminaries.html#9514" class="Field">pr₂</a> <a id="9518" class="Symbol">:</a> <a id="9520" href="Prelude.Preliminaries.html#9443" class="Bound">Y</a> <a id="9522" href="Prelude.Preliminaries.html#9503" class="Field">pr₁</a>

 <a id="9528" class="Keyword">infixr</a> <a id="9535" class="Number">50</a> <a id="9538" href="Prelude.Preliminaries.html#9488" class="InductiveConstructor Operator">_,_</a>

</pre>

For this dependent pair type, we prefer the notation `Σ x ꞉ X , y`, which is more pleasing and more standard than Agda's default syntax, `Σ λ(x ꞉ X) → y`.  [Escardó][] makes this preferred notation available in the [Type Topology][] library by making the index type explicit, as follows.

<pre class="Agda">

 <a id="hide-sigma.-Σ"></a><a id="9859" href="Prelude.Preliminaries.html#9859" class="Function">-Σ</a> <a id="9862" class="Symbol">:</a> <a id="9864" class="Symbol">{</a><a id="9865" href="Prelude.Preliminaries.html#9865" class="Bound">𝓤</a> <a id="9867" href="Prelude.Preliminaries.html#9867" class="Bound">𝓥</a> <a id="9869" class="Symbol">:</a> <a id="9871" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="9879" class="Symbol">}</a> <a id="9881" class="Symbol">(</a><a id="9882" href="Prelude.Preliminaries.html#9882" class="Bound">X</a> <a id="9884" class="Symbol">:</a> <a id="9886" href="Prelude.Preliminaries.html#9865" class="Bound">𝓤</a> <a id="9888" href="Universes.html#403" class="Function Operator">̇</a> <a id="9890" class="Symbol">)</a> <a id="9892" class="Symbol">(</a><a id="9893" href="Prelude.Preliminaries.html#9893" class="Bound">Y</a> <a id="9895" class="Symbol">:</a> <a id="9897" href="Prelude.Preliminaries.html#9882" class="Bound">X</a> <a id="9899" class="Symbol">→</a> <a id="9901" href="Prelude.Preliminaries.html#9867" class="Bound">𝓥</a> <a id="9903" href="Universes.html#403" class="Function Operator">̇</a> <a id="9905" class="Symbol">)</a> <a id="9907" class="Symbol">→</a> <a id="9909" href="Prelude.Preliminaries.html#9865" class="Bound">𝓤</a> <a id="9911" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="9913" href="Prelude.Preliminaries.html#9867" class="Bound">𝓥</a> <a id="9915" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="9918" href="Prelude.Preliminaries.html#9859" class="Function">-Σ</a> <a id="9921" href="Prelude.Preliminaries.html#9921" class="Bound">X</a> <a id="9923" href="Prelude.Preliminaries.html#9923" class="Bound">Y</a> <a id="9925" class="Symbol">=</a> <a id="9927" href="Prelude.Preliminaries.html#9423" class="Record">Σ</a> <a id="9929" href="Prelude.Preliminaries.html#9923" class="Bound">Y</a>

 <a id="9933" class="Keyword">syntax</a> <a id="9940" href="Prelude.Preliminaries.html#9859" class="Function">-Σ</a> <a id="9943" class="Bound">X</a> <a id="9945" class="Symbol">(λ</a> <a id="9948" class="Bound">x</a> <a id="9950" class="Symbol">→</a> <a id="9952" class="Bound">Y</a><a id="9953" class="Symbol">)</a> <a id="9955" class="Symbol">=</a> <a id="9957" class="Function">Σ</a> <a id="9959" class="Bound">x</a> <a id="9961" class="Function">꞉</a> <a id="9963" class="Bound">X</a> <a id="9965" class="Function">,</a> <a id="9967" class="Bound">Y</a>

</pre>

**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Σ x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].

A special case of the Sigma type is the one in which the type `Y` doesn't depend on `X`. This is the usual Cartesian product, defined in Agda as follows.

<pre class="Agda">

 <a id="hide-sigma._×_"></a><a id="10340" href="Prelude.Preliminaries.html#10340" class="Function Operator">_×_</a> <a id="10344" class="Symbol">:</a> <a id="10346" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10348" href="Universes.html#403" class="Function Operator">̇</a> <a id="10350" class="Symbol">→</a> <a id="10352" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10354" href="Universes.html#403" class="Function Operator">̇</a> <a id="10356" class="Symbol">→</a> <a id="10358" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="10360" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="10362" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="10364" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="10367" href="Prelude.Preliminaries.html#10367" class="Bound">X</a> <a id="10369" href="Prelude.Preliminaries.html#10340" class="Function Operator">×</a> <a id="10371" href="Prelude.Preliminaries.html#10371" class="Bound">Y</a> <a id="10373" class="Symbol">=</a> <a id="10375" href="Prelude.Preliminaries.html#9859" class="Function">Σ</a> <a id="10377" href="Prelude.Preliminaries.html#10377" class="Bound">x</a> <a id="10379" href="Prelude.Preliminaries.html#9859" class="Function">꞉</a> <a id="10381" href="Prelude.Preliminaries.html#10367" class="Bound">X</a> <a id="10383" href="Prelude.Preliminaries.html#9859" class="Function">,</a> <a id="10385" href="Prelude.Preliminaries.html#10371" class="Bound">Y</a>

</pre>


#### <a id="dependent-function-type">Pi types (dependent functions)</a>
Given universes `𝓤` and `𝓥`, a type `X : 𝓤 ̇`, and a type family `Y : X → 𝓥 ̇`, the *Pi type* (aka *dependent function type*) is denoted by `Π(x : X), Y x` and generalizes the function type `X → Y` by letting the type `Y x` of the codomain depend on the value `x` of the domain type. The dependent function type is defined in the [Type Topology][] in a standard way, but for the reader's benefit we repeat the definition here (inside a hidden module).<sup>[4](Prelude.Preliminaries.html#fn4)</sup>

<pre class="Agda">

<a id="10986" class="Keyword">module</a> <a id="hide-pi"></a><a id="10993" href="Prelude.Preliminaries.html#10993" class="Module">hide-pi</a> <a id="11001" class="Symbol">{</a><a id="11002" href="Prelude.Preliminaries.html#11002" class="Bound">𝓤</a> <a id="11004" href="Prelude.Preliminaries.html#11004" class="Bound">𝓦</a> <a id="11006" class="Symbol">:</a> <a id="11008" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="11016" class="Symbol">}</a> <a id="11018" class="Keyword">where</a>

 <a id="hide-pi.Π"></a><a id="11026" href="Prelude.Preliminaries.html#11026" class="Function">Π</a> <a id="11028" class="Symbol">:</a> <a id="11030" class="Symbol">{</a><a id="11031" href="Prelude.Preliminaries.html#11031" class="Bound">X</a> <a id="11033" class="Symbol">:</a> <a id="11035" href="Prelude.Preliminaries.html#11002" class="Bound">𝓤</a> <a id="11037" href="Universes.html#403" class="Function Operator">̇</a> <a id="11039" class="Symbol">}</a> <a id="11041" class="Symbol">(</a><a id="11042" href="Prelude.Preliminaries.html#11042" class="Bound">A</a> <a id="11044" class="Symbol">:</a> <a id="11046" href="Prelude.Preliminaries.html#11031" class="Bound">X</a> <a id="11048" class="Symbol">→</a> <a id="11050" href="Prelude.Preliminaries.html#11004" class="Bound">𝓦</a> <a id="11052" href="Universes.html#403" class="Function Operator">̇</a> <a id="11054" class="Symbol">)</a> <a id="11056" class="Symbol">→</a> <a id="11058" href="Prelude.Preliminaries.html#11002" class="Bound">𝓤</a> <a id="11060" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11062" href="Prelude.Preliminaries.html#11004" class="Bound">𝓦</a> <a id="11064" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11067" href="Prelude.Preliminaries.html#11026" class="Function">Π</a> <a id="11069" class="Symbol">{</a><a id="11070" href="Prelude.Preliminaries.html#11070" class="Bound">X</a><a id="11071" class="Symbol">}</a> <a id="11073" href="Prelude.Preliminaries.html#11073" class="Bound">A</a> <a id="11075" class="Symbol">=</a> <a id="11077" class="Symbol">(</a><a id="11078" href="Prelude.Preliminaries.html#11078" class="Bound">x</a> <a id="11080" class="Symbol">:</a> <a id="11082" href="Prelude.Preliminaries.html#11070" class="Bound">X</a><a id="11083" class="Symbol">)</a> <a id="11085" class="Symbol">→</a> <a id="11087" href="Prelude.Preliminaries.html#11073" class="Bound">A</a> <a id="11089" href="Prelude.Preliminaries.html#11078" class="Bound">x</a>

 <a id="hide-pi.-Π"></a><a id="11093" href="Prelude.Preliminaries.html#11093" class="Function">-Π</a> <a id="11096" class="Symbol">:</a> <a id="11098" class="Symbol">(</a><a id="11099" href="Prelude.Preliminaries.html#11099" class="Bound">X</a> <a id="11101" class="Symbol">:</a> <a id="11103" href="Prelude.Preliminaries.html#11002" class="Bound">𝓤</a> <a id="11105" href="Universes.html#403" class="Function Operator">̇</a> <a id="11107" class="Symbol">)(</a><a id="11109" href="Prelude.Preliminaries.html#11109" class="Bound">Y</a> <a id="11111" class="Symbol">:</a> <a id="11113" href="Prelude.Preliminaries.html#11099" class="Bound">X</a> <a id="11115" class="Symbol">→</a> <a id="11117" href="Prelude.Preliminaries.html#11004" class="Bound">𝓦</a> <a id="11119" href="Universes.html#403" class="Function Operator">̇</a> <a id="11121" class="Symbol">)</a> <a id="11123" class="Symbol">→</a> <a id="11125" href="Prelude.Preliminaries.html#11002" class="Bound">𝓤</a> <a id="11127" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="11129" href="Prelude.Preliminaries.html#11004" class="Bound">𝓦</a> <a id="11131" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="11134" href="Prelude.Preliminaries.html#11093" class="Function">-Π</a> <a id="11137" href="Prelude.Preliminaries.html#11137" class="Bound">X</a> <a id="11139" href="Prelude.Preliminaries.html#11139" class="Bound">Y</a> <a id="11141" class="Symbol">=</a> <a id="11143" href="Prelude.Preliminaries.html#11026" class="Function">Π</a> <a id="11145" href="Prelude.Preliminaries.html#11139" class="Bound">Y</a>

 <a id="11149" class="Keyword">infixr</a> <a id="11156" class="Number">-1</a> <a id="11159" href="Prelude.Preliminaries.html#11093" class="Function">-Π</a>
 <a id="11163" class="Keyword">syntax</a> <a id="11170" href="Prelude.Preliminaries.html#11093" class="Function">-Π</a> <a id="11173" class="Bound">A</a> <a id="11175" class="Symbol">(λ</a> <a id="11178" class="Bound">x</a> <a id="11180" class="Symbol">→</a> <a id="11182" class="Bound">b</a><a id="11183" class="Symbol">)</a> <a id="11185" class="Symbol">=</a> <a id="11187" class="Function">Π</a> <a id="11189" class="Bound">x</a> <a id="11191" class="Function">꞉</a> <a id="11193" class="Bound">A</a> <a id="11195" class="Function">,</a> <a id="11197" class="Bound">b</a>

</pre>

To make the syntax for `Π` conform to the standard notation for *Pi types* (or dependent function type), [Escardó][] uses the same trick as the one used above for *Sigma types*.


Now that we have studied these important types, defined in the [Type Topology][] library and repeated here for illustration purposes, let us import the original definitions with the `public` directive so that they are available to all modules importing [Prelude.Preliminaries][].

<pre class="Agda">

<a id="11687" class="Keyword">open</a> <a id="11692" class="Keyword">import</a> <a id="11699" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="11710" class="Keyword">renaming</a> <a id="11719" class="Symbol">(</a><a id="11720" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a> <a id="11724" class="Symbol">to</a> <a id="11727" class="Keyword">infixr</a> <a id="11734" class="Number">50</a> <a id="_,_"></a><a id="11737" href="Prelude.Preliminaries.html#11737" class="InductiveConstructor Operator">_,_</a><a id="11740" class="Symbol">)</a> <a id="11742" class="Keyword">public</a>
<a id="11749" class="Keyword">open</a> <a id="11754" class="Keyword">import</a> <a id="11761" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="11770" class="Keyword">using</a> <a id="11776" class="Symbol">(</a><a id="11777" href="MGS-MLTT.html#2942" class="Function">pr₁</a><a id="11780" class="Symbol">;</a> <a id="11782" href="MGS-MLTT.html#3001" class="Function">pr₂</a><a id="11785" class="Symbol">;</a> <a id="11787" href="MGS-MLTT.html#3515" class="Function Operator">_×_</a><a id="11790" class="Symbol">;</a> <a id="11792" href="MGS-MLTT.html#3074" class="Function">-Σ</a><a id="11794" class="Symbol">;</a> <a id="11796" href="MGS-MLTT.html#3562" class="Function">Π</a><a id="11797" class="Symbol">;</a> <a id="11799" href="MGS-MLTT.html#3635" class="Function">-Π</a><a id="11801" class="Symbol">)</a> <a id="11803" class="Keyword">public</a>

</pre>

##### Notation for the first and second projections

The definition of `Σ` (and thus, of `×`) includes the fields `pr₁` and `pr₂` representing the first and second projections out of the product.  Sometimes we prefer to denote these projections by `∣\_∣` and `∥\_∥` respectively. However, for emphasis or readability we alternate between these and the following standard notations: `pr₁` and `fst` for the first projection, `pr₂` and `snd` for the second.  We define these alternative notations for projections out of pairs as follows.

<pre class="Agda">

<a id="12374" class="Keyword">module</a> <a id="12381" href="Prelude.Preliminaries.html#12381" class="Module">_</a> <a id="12383" class="Symbol">{</a><a id="12384" href="Prelude.Preliminaries.html#12384" class="Bound">𝓤</a> <a id="12386" class="Symbol">:</a> <a id="12388" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="12396" class="Symbol">}</a> <a id="12398" class="Keyword">where</a>

 <a id="12406" href="Prelude.Preliminaries.html#12406" class="Function Operator">∣_∣</a> <a id="12410" href="Prelude.Preliminaries.html#12410" class="Function">fst</a> <a id="12414" class="Symbol">:</a> <a id="12416" class="Symbol">{</a><a id="12417" href="Prelude.Preliminaries.html#12417" class="Bound">X</a> <a id="12419" class="Symbol">:</a> <a id="12421" href="Prelude.Preliminaries.html#12384" class="Bound">𝓤</a> <a id="12423" href="Universes.html#403" class="Function Operator">̇</a> <a id="12425" class="Symbol">}{</a><a id="12427" href="Prelude.Preliminaries.html#12427" class="Bound">Y</a> <a id="12429" class="Symbol">:</a> <a id="12431" href="Prelude.Preliminaries.html#12417" class="Bound">X</a> <a id="12433" class="Symbol">→</a> <a id="12435" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12437" href="Universes.html#403" class="Function Operator">̇</a><a id="12438" class="Symbol">}</a> <a id="12440" class="Symbol">→</a> <a id="12442" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12444" href="Prelude.Preliminaries.html#12427" class="Bound">Y</a> <a id="12446" class="Symbol">→</a> <a id="12448" href="Prelude.Preliminaries.html#12417" class="Bound">X</a>
 <a id="12451" href="Prelude.Preliminaries.html#12406" class="Function Operator">∣</a> <a id="12453" href="Prelude.Preliminaries.html#12453" class="Bound">x</a> <a id="12455" href="Prelude.Preliminaries.html#11737" class="InductiveConstructor Operator">,</a> <a id="12457" href="Prelude.Preliminaries.html#12457" class="Bound">y</a> <a id="12459" href="Prelude.Preliminaries.html#12406" class="Function Operator">∣</a> <a id="12461" class="Symbol">=</a> <a id="12463" href="Prelude.Preliminaries.html#12453" class="Bound">x</a>
 <a id="12466" href="Prelude.Preliminaries.html#12410" class="Function">fst</a> <a id="12470" class="Symbol">(</a><a id="12471" href="Prelude.Preliminaries.html#12471" class="Bound">x</a> <a id="12473" href="Prelude.Preliminaries.html#11737" class="InductiveConstructor Operator">,</a> <a id="12475" href="Prelude.Preliminaries.html#12475" class="Bound">y</a><a id="12476" class="Symbol">)</a> <a id="12478" class="Symbol">=</a> <a id="12480" href="Prelude.Preliminaries.html#12471" class="Bound">x</a>

 <a id="12484" href="Prelude.Preliminaries.html#12484" class="Function Operator">∥_∥</a> <a id="12488" href="Prelude.Preliminaries.html#12488" class="Function">snd</a> <a id="12492" class="Symbol">:</a> <a id="12494" class="Symbol">{</a><a id="12495" href="Prelude.Preliminaries.html#12495" class="Bound">X</a> <a id="12497" class="Symbol">:</a> <a id="12499" href="Prelude.Preliminaries.html#12384" class="Bound">𝓤</a> <a id="12501" href="Universes.html#403" class="Function Operator">̇</a> <a id="12503" class="Symbol">}{</a><a id="12505" href="Prelude.Preliminaries.html#12505" class="Bound">Y</a> <a id="12507" class="Symbol">:</a> <a id="12509" href="Prelude.Preliminaries.html#12495" class="Bound">X</a> <a id="12511" class="Symbol">→</a> <a id="12513" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="12515" href="Universes.html#403" class="Function Operator">̇</a> <a id="12517" class="Symbol">}</a> <a id="12519" class="Symbol">→</a> <a id="12521" class="Symbol">(</a><a id="12522" href="Prelude.Preliminaries.html#12522" class="Bound">z</a> <a id="12524" class="Symbol">:</a> <a id="12526" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="12528" href="Prelude.Preliminaries.html#12505" class="Bound">Y</a><a id="12529" class="Symbol">)</a> <a id="12531" class="Symbol">→</a> <a id="12533" href="Prelude.Preliminaries.html#12505" class="Bound">Y</a> <a id="12535" class="Symbol">(</a><a id="12536" href="MGS-MLTT.html#2942" class="Function">pr₁</a> <a id="12540" href="Prelude.Preliminaries.html#12522" class="Bound">z</a><a id="12541" class="Symbol">)</a>
 <a id="12544" href="Prelude.Preliminaries.html#12484" class="Function Operator">∥</a> <a id="12546" href="Prelude.Preliminaries.html#12546" class="Bound">x</a> <a id="12548" href="Prelude.Preliminaries.html#11737" class="InductiveConstructor Operator">,</a> <a id="12550" href="Prelude.Preliminaries.html#12550" class="Bound">y</a> <a id="12552" href="Prelude.Preliminaries.html#12484" class="Function Operator">∥</a> <a id="12554" class="Symbol">=</a> <a id="12556" href="Prelude.Preliminaries.html#12550" class="Bound">y</a>
 <a id="12559" href="Prelude.Preliminaries.html#12488" class="Function">snd</a> <a id="12563" class="Symbol">(</a><a id="12564" href="Prelude.Preliminaries.html#12564" class="Bound">x</a> <a id="12566" href="Prelude.Preliminaries.html#11737" class="InductiveConstructor Operator">,</a> <a id="12568" href="Prelude.Preliminaries.html#12568" class="Bound">y</a><a id="12569" class="Symbol">)</a> <a id="12571" class="Symbol">=</a> <a id="12573" href="Prelude.Preliminaries.html#12568" class="Bound">y</a>

</pre>

Here we put the definitions inside an *anonymous module*, which starts with the `module` keyword followed by an underscore (instead of a module name). The purpose is simply to move the postulated typing judgments---the "parameters" of the module (e.g., `𝓤 : Universe`)---out of the way so they don't obfuscate the definitions inside the module.


----------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> [Martín Escardó][] has written an outstanding set of notes called \href{https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html}{Introduction to Univalent Foundations of Mathematics with Agda}, which we highly recommend to anyone wanting more details than we provide here about [MLTT][] and Univalent Foundations/HoTT in Agda.

<sup>2</sup><span class="footnote" id="fn2"> We won't discuss every line of the `Universes.lagda` file; instead we merely highlight the few lines of code from the `Universes` module that define the notational devices adopted throughout the UALib. For more details we refer readers to [Martin Escardo's notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes).</span>

<sup>3</sup><span class="footnote" id="fn3">To hide code from the rest of the development, we enclose it in a named module.  For example, the code inside the `hide-refl` module will not conflict with the original definitions from the [Type Topology][] library as long as we don't invoke `open hide-refl`. It may seem odd to define something in a hidden module only to import and use an alternative definition, but we do so in order to exhibit all of the types on which the [UALib][] depends while ensuring that this is not misinterpreted as a claim to originality.</span>

<sup>4</sup><span class="footnote" id="fn4">**WARNING!** The symbol ꞉ is not the same as : despite how similar they may appear. The correct colon in the expression `Π x ꞉ X , y` above is obtained by typing `\:4` in [agda2-mode][].</sup>


<br>
<br>

[↑ Prelude](Prelude.html)
<span style="float:right;">[Prelude.Equality →](Prelude.Equality.html)</span>


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
