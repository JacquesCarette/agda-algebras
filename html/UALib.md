---
layout: title-page
title : The Agda Universal Algebra Library (UAlib)
date : 2021-01-14
author: William DeMeo
---

<!--

FILE      : UALib.lagda
AUTHOR    : William DeMeo  <williamdemeo@gmail.com>
DATED     : 14 Jan 2021
UPDATED   : 15 Jan 2021
COPYRIGHT : (c) 2021 William DeMeo

[The Agda Universal Algebra Library](UALib.html)

LICENSE:

The software in this file is subject to the GNU General Public License v3.0.

See the LICENSE file at https://gitlab.com/ualib/ualib.gitlab.io/-/blob/master/LICENSE

The text other than software is copyright of the author. It can be
used for scholarly purposes subject to the usual academic conventions
of citation.

* The *.lagda files are not meant to be read by people, but rather to be
  type-checked by the Agda proof assistant and to automatically generate html files
  (which are meant to be read by people).

* This is done with the generatehtml file to generate markdown and html files from the
  literate Agda (.lagda) files, and then using jekyll to convert markdown into html.

-->

## <a id="ualib">The Agda Universal Algebra Library</a>

---------------------------------------------------------------------------------

(version 2.01 of {{ "now" | date: "%d %b %Y" }})

**Author**. [William DeMeo][]  
*Affiliation*. [Department of Algebra][], [Charles University in Prague][]

**Abstract**. The [Agda Universal Algebra Library][] ([Agda UALib][]) is a library of types and programs (theorems and proofs) that formalizes the foundations of universal algebra in Martin-Löf type theory using the [Agda][] proof assistant language.

In the latest version of the library we have defined many new types for representing the important constructs and theorems that comprise part of the foundations of general (universal) algebra and equational logic. These types are implemented in so called "literate" Agda files, with the `.lagda` extension, and they are grouped into modules so that they may be easily imported into other Agda programs.

To give an idea of the current scope of the library, we note that it now includes a complete proof of the [Birkhoff HSP Theorem](UALib.Birkhoff.Theorem.html) which asserts that every variety is an equational class.  That is, if K is a class of algebras that is closed under the taking of homomorphic images, subalgebras, and arbitrary products, then K is the class of algebras satisfying some set of identities. To our knowledge, ours is the first formal, constructive, machine-checked proof of Birkhoff's Theorem.<span class="footnote"><sup>1</sup></span>

We hope the library will be useful to research mathematicians and computer scientists who wish to verify their work by formalizing and type-checking the theorems they prove. Moreover, the [Agda UALib][] is (or wants to be when it grows up) an indispensable guide on our mathematical journies, helping us forge new paths, reach higher peaks, and authenticating what we believe we have found.

--------------------------------

### <a id="brief-contents"></a> Brief Contents

<pre class="Agda">

<a id="3042" class="Symbol">{-#</a> <a id="3046" class="Keyword">OPTIONS</a> <a id="3054" class="Pragma">--without-K</a> <a id="3066" class="Pragma">--exact-split</a> <a id="3080" class="Pragma">--safe</a> <a id="3087" class="Symbol">#-}</a>

<a id="3092" class="Keyword">module</a> <a id="3099" href="UALib.html" class="Module">UALib</a> <a id="3105" class="Keyword">where</a>

<a id="3112" class="Keyword">open</a> <a id="3117" class="Keyword">import</a> <a id="3124" href="UALib.Preface.html" class="Module">UALib.Preface</a>
<a id="3138" class="Keyword">open</a> <a id="3143" class="Keyword">import</a> <a id="3150" href="UALib.Prelude.html" class="Module">UALib.Prelude</a>
<a id="3164" class="Keyword">open</a> <a id="3169" class="Keyword">import</a> <a id="3176" href="UALib.Algebras.html" class="Module">UALib.Algebras</a>
<a id="3191" class="Keyword">open</a> <a id="3196" class="Keyword">import</a> <a id="3203" href="UALib.Relations.html" class="Module">UALib.Relations</a>
<a id="3219" class="Keyword">open</a> <a id="3224" class="Keyword">import</a> <a id="3231" href="UALib.Homomorphisms.html" class="Module">UALib.Homomorphisms</a>
<a id="3251" class="Keyword">open</a> <a id="3256" class="Keyword">import</a> <a id="3263" href="UALib.Terms.html" class="Module">UALib.Terms</a>
<a id="3275" class="Keyword">open</a> <a id="3280" class="Keyword">import</a> <a id="3287" href="UALib.Subalgebras.html" class="Module">UALib.Subalgebras</a>
<a id="3305" class="Keyword">open</a> <a id="3310" class="Keyword">import</a> <a id="3317" href="UALib.Varieties.html" class="Module">UALib.Varieties</a>
<a id="3333" class="Keyword">open</a> <a id="3338" class="Keyword">import</a> <a id="3345" href="UALib.Birkhoff.html" class="Module">UALib.Birkhoff</a>

</pre>

-------------------------------------------

### <a id="detailed-contents"></a> Detailed Contents

- [Preface](UALib.Preface.html)

- [Prelude](UALib.Prelude.html)
  - [Preliminaries](UALib.Prelude.Preliminaries.html)
  - [Equality](UALib.Prelude.Equality.html)
  - [Inverses](UALib.Prelude.Inverses.html)
  - [Extensionality](UALib.Prelude.Extensionality.html)

- [Algebras](UALib.Algebras.html)
  - [Operation and Signature Types](UALib.Algebras.Signatures.html)
  - [Algebra Types](UALib.Algebras.Algebras.html)
  - [Product Algebra Types](UALib.Algebras.Products.html)
  - [Agda's Universe Hierarchy](UALib.Algebras.Lifts.html)

- [Relations](UALib.Relations.html)
  - [Unary Relation Types](UALib.Relations.Unary.html)
  - [Binary Relation and Kernel Types](UALib.Relations.Binary.html)
  - [Equivalence Relation Types](UALib.Relations.Equivalences.html)
  - [Quotient Types](UALib.Relations.Quotients.html)
  - [Congruence Relation Types](UALib.Relations.Congruences.html)

- [Homomorphisms](UALib.Homomorphisms.html)
  - [Basic definitions](UALib.Homomorphisms.Basic.html)
  - [Kernels of Homomorphisms](UALib.Homomorphisms.Kernels.html)
  - [Homomorphism Theorems](UALib.Homomorphisms.Noether.html)
  - [Homomorphisms and Products](UALib.Homomorphisms.Products.html)
  - [Isomorphism Type](UALib.Homomorphisms.Isomorphisms.html)
  - [Homomorphic Image Types](UALib.Homomorphisms.HomomorphicImages.html)

- [Terms and Free Algebras](UALib.Terms.html)
  - [Basic Definitions](UALib.Terms.Basic.html)
  - [The Term Algebra](UALib.Terms.Free.html)
  - [Term Operation Types](UALib.Terms.Operations.html)
  - [Term Compatibility Theorems](UALib.Terms.Compatibility.html)

- [Subalgebras](UALib.Subalgebras.html)
  - [Subuniverse Types](UALib.Subalgebras.Subuniverses.html)
  - [Inductive Types for Subuniverse Generation](UALib.Subalgebras.Generation.html)
  - [Subuniverse Lemmas](UALib.Subalgebras.Properties.html)
  - [Subuniverses and Homomorphisms](UALib.Subalgebras.Homomorphisms.html)
  - [Subalgebra Types](UALib.Subalgebras.Subalgebras)
  - [WWMD](UALib.Subalgebras.WWMD.html)

- [Equations and Varieties](UALib.Varieties.html)
  - [Types for Theories and Models](UALib.Varieties.ModelTheory.html)
  - [Equational Logic Types](UALib.Varieties.EquationalLogic.html)
  - [Inductive Types H, S, P, V](UALib.Varieties.Varieties.html)
  - [Equation Preservation Theorems](UALib.Varieties.Preservation.html)

- [Birkhoff's Theorem](UALib.Birkhoff.html)
  - [Relatively Free Algebra Types](UALib.Birkhoff.FreeAlgebra.html)
  - [HSP Lemmata](UALib.Birkhoff.Lemmata.html)
  - [HSP Theorem](UALib.Birkhoff.Theorem.html)

---------------------------------------

<span class="footnote"><sup>1</sup>[Contact the author](mailto:williamdemeo@gmail.com) if you find any evidence that refutes this claim.</span>

<p></p>

<span style="float:right;">[Next Module (UALib.Preface) →](UALib.Preface.html)</span>


<div class="container">
<p>
<i>Updated {{ "now" | date: "%d %b %Y, %H:%M" }}</i>
</p>
</div>


{% include UALib.Links.md %}
