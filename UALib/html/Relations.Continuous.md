---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="big-relations">Continuous Relations</a>

This section presents the [UALib.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `GenRel` to be the type `(I → A) → 𝓦 ̇` and we will call `GenRel` the type of **general relations**.  This generalizes the unary and binary relations we saw earlier in the sense that general relations can have arbitrarily large arities. However, relations of type `GenRel` are not completely general because they are defined over a single type.

Just as `Rel A 𝓦` was the "single-sorted" special case of the "multisorted" `REL A B 𝓦` type, so too will `GenRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇ ` of types, we may have a relation from `A i` to `A i'` to `A i''` to ….  We will refer to such relations as **dependent relations** because in order to define a type to represent them, we absolutely need depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) captures this completely general notion of relation.

<pre class="Agda">

<a id="2129" class="Symbol">{-#</a> <a id="2133" class="Keyword">OPTIONS</a> <a id="2141" class="Pragma">--without-K</a> <a id="2153" class="Pragma">--exact-split</a> <a id="2167" class="Pragma">--safe</a> <a id="2174" class="Symbol">#-}</a>

<a id="2179" class="Keyword">module</a> <a id="2186" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="2207" class="Keyword">where</a>

<a id="2214" class="Keyword">open</a> <a id="2219" class="Keyword">import</a> <a id="2226" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="2245" class="Keyword">public</a>

</pre>

#### <a id="general-relations">General relations</a>

In this subsection we define the type `GenRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **general relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="GenRel"></a><a id="2852" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="2859" class="Symbol">:</a> <a id="2861" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2863" href="Universes.html#403" class="Function Operator">̇</a> <a id="2865" class="Symbol">→</a> <a id="2867" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2869" href="Universes.html#403" class="Function Operator">̇</a> <a id="2871" class="Symbol">→</a> <a id="2873" class="Symbol">(</a><a id="2874" href="Relations.Continuous.html#2874" class="Bound">𝓦</a> <a id="2876" class="Symbol">:</a> <a id="2878" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2886" class="Symbol">)</a> <a id="2888" class="Symbol">→</a> <a id="2890" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2892" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2894" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2896" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2898" href="Relations.Continuous.html#2874" class="Bound">𝓦</a> <a id="2900" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="2902" href="Universes.html#403" class="Function Operator">̇</a>
<a id="2904" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="2911" href="Relations.Continuous.html#2911" class="Bound">I</a> <a id="2913" href="Relations.Continuous.html#2913" class="Bound">A</a> <a id="2915" href="Relations.Continuous.html#2915" class="Bound">𝓦</a> <a id="2917" class="Symbol">=</a> <a id="2919" class="Symbol">(</a><a id="2920" href="Relations.Continuous.html#2911" class="Bound">I</a> <a id="2922" class="Symbol">→</a> <a id="2924" href="Relations.Continuous.html#2913" class="Bound">A</a><a id="2925" class="Symbol">)</a> <a id="2927" class="Symbol">→</a> <a id="2929" href="Relations.Continuous.html#2915" class="Bound">𝓦</a> <a id="2931" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with general relations.

<pre class="Agda">

<a id="3181" class="Keyword">module</a> <a id="3188" href="Relations.Continuous.html#3188" class="Module">_</a> <a id="3190" class="Symbol">{</a><a id="3191" href="Relations.Continuous.html#3191" class="Bound">𝓤</a> <a id="3193" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3195" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3197" class="Symbol">:</a> <a id="3199" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3207" class="Symbol">}</a> <a id="3209" class="Symbol">{</a><a id="3210" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3212" href="Relations.Continuous.html#3212" class="Bound">J</a> <a id="3214" class="Symbol">:</a> <a id="3216" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3218" href="Universes.html#403" class="Function Operator">̇</a><a id="3219" class="Symbol">}</a> <a id="3221" class="Symbol">{</a><a id="3222" href="Relations.Continuous.html#3222" class="Bound">A</a> <a id="3224" class="Symbol">:</a> <a id="3226" href="Relations.Continuous.html#3191" class="Bound">𝓤</a> <a id="3228" href="Universes.html#403" class="Function Operator">̇</a><a id="3229" class="Symbol">}</a> <a id="3231" class="Keyword">where</a>

 <a id="3239" href="Relations.Continuous.html#3239" class="Function">lift-gen-rel</a> <a id="3252" class="Symbol">:</a> <a id="3254" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="3261" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3263" href="Relations.Continuous.html#3222" class="Bound">A</a> <a id="3265" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3267" class="Symbol">→</a> <a id="3269" class="Symbol">(</a><a id="3270" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3272" class="Symbol">→</a> <a id="3274" href="Relations.Continuous.html#3212" class="Bound">J</a> <a id="3276" class="Symbol">→</a> <a id="3278" href="Relations.Continuous.html#3222" class="Bound">A</a><a id="3279" class="Symbol">)</a> <a id="3281" class="Symbol">→</a> <a id="3283" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3285" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3287" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3289" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3292" href="Relations.Continuous.html#3239" class="Function">lift-gen-rel</a> <a id="3305" href="Relations.Continuous.html#3305" class="Bound">R</a> <a id="3307" href="Relations.Continuous.html#3307" class="Bound">𝕒</a> <a id="3309" class="Symbol">=</a> <a id="3311" class="Symbol">∀</a> <a id="3313" class="Symbol">(</a><a id="3314" href="Relations.Continuous.html#3314" class="Bound">j</a> <a id="3316" class="Symbol">:</a> <a id="3318" href="Relations.Continuous.html#3212" class="Bound">J</a><a id="3319" class="Symbol">)</a> <a id="3321" class="Symbol">→</a> <a id="3323" href="Relations.Continuous.html#3305" class="Bound">R</a> <a id="3325" class="Symbol">λ</a> <a id="3327" href="Relations.Continuous.html#3327" class="Bound">i</a> <a id="3329" class="Symbol">→</a> <a id="3331" class="Symbol">(</a><a id="3332" href="Relations.Continuous.html#3307" class="Bound">𝕒</a> <a id="3334" href="Relations.Continuous.html#3327" class="Bound">i</a><a id="3335" class="Symbol">)</a> <a id="3337" href="Relations.Continuous.html#3314" class="Bound">j</a>

 <a id="3341" href="Relations.Continuous.html#3341" class="Function">gen-compatible-fun</a> <a id="3360" class="Symbol">:</a> <a id="3362" class="Symbol">(</a><a id="3363" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3365" class="Symbol">→</a> <a id="3367" class="Symbol">(</a><a id="3368" href="Relations.Continuous.html#3212" class="Bound">J</a> <a id="3370" class="Symbol">→</a> <a id="3372" href="Relations.Continuous.html#3222" class="Bound">A</a><a id="3373" class="Symbol">)</a> <a id="3375" class="Symbol">→</a> <a id="3377" href="Relations.Continuous.html#3222" class="Bound">A</a><a id="3378" class="Symbol">)</a> <a id="3380" class="Symbol">→</a> <a id="3382" href="Relations.Continuous.html#2852" class="Function">GenRel</a> <a id="3389" href="Relations.Continuous.html#3210" class="Bound">I</a> <a id="3391" href="Relations.Continuous.html#3222" class="Bound">A</a> <a id="3393" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3395" class="Symbol">→</a> <a id="3397" href="Relations.Continuous.html#3193" class="Bound">𝓥</a> <a id="3399" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3401" href="Relations.Continuous.html#3191" class="Bound">𝓤</a> <a id="3403" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3405" href="Relations.Continuous.html#3195" class="Bound">𝓦</a> <a id="3407" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3410" href="Relations.Continuous.html#3341" class="Function">gen-compatible-fun</a> <a id="3429" href="Relations.Continuous.html#3429" class="Bound">𝕗</a> <a id="3431" href="Relations.Continuous.html#3431" class="Bound">R</a>  <a id="3434" class="Symbol">=</a> <a id="3436" class="Symbol">∀</a> <a id="3438" href="Relations.Continuous.html#3438" class="Bound">𝕒</a> <a id="3440" class="Symbol">→</a> <a id="3442" class="Symbol">(</a><a id="3443" href="Relations.Continuous.html#3239" class="Function">lift-gen-rel</a> <a id="3456" href="Relations.Continuous.html#3431" class="Bound">R</a><a id="3457" class="Symbol">)</a> <a id="3459" href="Relations.Continuous.html#3438" class="Bound">𝕒</a> <a id="3461" class="Symbol">→</a> <a id="3463" href="Relations.Continuous.html#3431" class="Bound">R</a> <a id="3465" class="Symbol">λ</a> <a id="3467" href="Relations.Continuous.html#3467" class="Bound">i</a> <a id="3469" class="Symbol">→</a> <a id="3471" class="Symbol">(</a><a id="3472" href="Relations.Continuous.html#3429" class="Bound">𝕗</a> <a id="3474" href="Relations.Continuous.html#3467" class="Bound">i</a><a id="3475" class="Symbol">)</a> <a id="3477" class="Symbol">(</a><a id="3478" href="Relations.Continuous.html#3438" class="Bound">𝕒</a> <a id="3480" href="Relations.Continuous.html#3467" class="Bound">i</a><a id="3481" class="Symbol">)</a>

</pre>

In the definition of `gen-compatible-fun`, we let Agda infer the type of `𝕒`, which is `I → (J → A)`.

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics instead of the semantics.  In fact, we should probably pause here to discuss these semantics, lest the more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝕒 : I → (J → A)` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, recall that a general relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Next consider the function `lift-gen-rel`.  For each general relation `R`, the type `lift-gen-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝕒 : I → (J → A)` such that `lift-gen-rel R 𝕒` holds.

It helps to visualize such `J`-tuples as columns and imagine for simplicity that `J` is a finite set, say, `{1, 2, ..., J}`.  Picture a couple of these columns, say, the i-th and k-th, like so.

```
𝕒 i 1      𝕒 k 1
𝕒 i 2      𝕒 k 2
𝕒 i 3      𝕒 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝕒 i J      𝕒 k J
```

Now `lift-gen-rel R 𝕒` is defined by `∀ j → R (λ i → (𝕒 i) j)` which represents the assertion that each row of the `I` columns shown above (which evidently is an `I`-tuple) belongs to the original relation `R`.

Next, let's dissect the definition of `gen-compatible-fun`.  Here, `𝕗 : I → (J → A) → A` denotes an `I`-tuple of `J`-ary operations on `A`.  That is, for each `i : I`, the function `𝕗 i` takes a `J`-tuple `𝕒 i : J → A` and evaluates to some `(𝕗 i) (𝕒 i) : A`.

Finally, digest all the types involved in these definitions and note how nicely they align (as they must if type-checking is to succeed!).  For example, `𝕒 : I → (J → A)` is precisely the type on which the relation `lift-gen-rel R` is defined.


#### <a id="dependent-relations">Dependent relations</a>

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `A i₁` to `A i₂` to `A i₃` to …  (This is just for intuition, of course, since the domain `I` may not even be enumerable).

<pre class="Agda">

<a id="DepRel"></a><a id="6045" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6052" class="Symbol">:</a> <a id="6054" class="Symbol">(</a><a id="6055" href="Relations.Continuous.html#6055" class="Bound">I</a> <a id="6057" class="Symbol">:</a> <a id="6059" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6061" href="Universes.html#403" class="Function Operator">̇</a><a id="6062" class="Symbol">)(</a><a id="6064" href="Relations.Continuous.html#6064" class="Bound">A</a> <a id="6066" class="Symbol">:</a> <a id="6068" href="Relations.Continuous.html#6055" class="Bound">I</a> <a id="6070" class="Symbol">→</a> <a id="6072" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6074" href="Universes.html#403" class="Function Operator">̇</a><a id="6075" class="Symbol">)(</a><a id="6077" href="Relations.Continuous.html#6077" class="Bound">𝓦</a> <a id="6079" class="Symbol">:</a> <a id="6081" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6089" class="Symbol">)</a> <a id="6091" class="Symbol">→</a> <a id="6093" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6095" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6097" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6099" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6101" href="Relations.Continuous.html#6077" class="Bound">𝓦</a> <a id="6103" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="6105" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6107" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6114" href="Relations.Continuous.html#6114" class="Bound">I</a> <a id="6116" href="Relations.Continuous.html#6116" class="Bound">A</a> <a id="6118" href="Relations.Continuous.html#6118" class="Bound">𝓦</a> <a id="6120" class="Symbol">=</a> <a id="6122" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6124" href="Relations.Continuous.html#6116" class="Bound">A</a> <a id="6126" class="Symbol">→</a> <a id="6128" href="Relations.Continuous.html#6118" class="Bound">𝓦</a> <a id="6130" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

Above we made peace with lifts of general relations and what it means for such relations to be compatibile with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="6627" class="Keyword">module</a> <a id="6634" href="Relations.Continuous.html#6634" class="Module">_</a> <a id="6636" class="Symbol">{</a><a id="6637" href="Relations.Continuous.html#6637" class="Bound">𝓤</a> <a id="6639" href="Relations.Continuous.html#6639" class="Bound">𝓥</a> <a id="6641" href="Relations.Continuous.html#6641" class="Bound">𝓦</a> <a id="6643" class="Symbol">:</a> <a id="6645" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6653" class="Symbol">}</a> <a id="6655" class="Symbol">{</a><a id="6656" href="Relations.Continuous.html#6656" class="Bound">I</a> <a id="6658" href="Relations.Continuous.html#6658" class="Bound">J</a> <a id="6660" class="Symbol">:</a> <a id="6662" href="Relations.Continuous.html#6639" class="Bound">𝓥</a> <a id="6664" href="Universes.html#403" class="Function Operator">̇</a><a id="6665" class="Symbol">}</a> <a id="6667" class="Symbol">{</a><a id="6668" href="Relations.Continuous.html#6668" class="Bound">A</a> <a id="6670" class="Symbol">:</a> <a id="6672" href="Relations.Continuous.html#6656" class="Bound">I</a> <a id="6674" class="Symbol">→</a> <a id="6676" href="Relations.Continuous.html#6637" class="Bound">𝓤</a> <a id="6678" href="Universes.html#403" class="Function Operator">̇</a><a id="6679" class="Symbol">}</a> <a id="6681" class="Keyword">where</a>

 <a id="6689" href="Relations.Continuous.html#6689" class="Function">lift-dep-rel</a> <a id="6702" class="Symbol">:</a> <a id="6704" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6711" href="Relations.Continuous.html#6656" class="Bound">I</a> <a id="6713" href="Relations.Continuous.html#6668" class="Bound">A</a> <a id="6715" href="Relations.Continuous.html#6641" class="Bound">𝓦</a> <a id="6717" class="Symbol">→</a> <a id="6719" class="Symbol">(∀</a> <a id="6722" href="Relations.Continuous.html#6722" class="Bound">i</a> <a id="6724" class="Symbol">→</a> <a id="6726" href="Relations.Continuous.html#6658" class="Bound">J</a> <a id="6728" class="Symbol">→</a> <a id="6730" href="Relations.Continuous.html#6668" class="Bound">A</a> <a id="6732" href="Relations.Continuous.html#6722" class="Bound">i</a><a id="6733" class="Symbol">)</a> <a id="6735" class="Symbol">→</a> <a id="6737" href="Relations.Continuous.html#6639" class="Bound">𝓥</a> <a id="6739" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6741" href="Relations.Continuous.html#6641" class="Bound">𝓦</a> <a id="6743" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6746" href="Relations.Continuous.html#6689" class="Function">lift-dep-rel</a> <a id="6759" href="Relations.Continuous.html#6759" class="Bound">R</a> <a id="6761" href="Relations.Continuous.html#6761" class="Bound">𝕒</a> <a id="6763" class="Symbol">=</a> <a id="6765" class="Symbol">∀</a> <a id="6767" class="Symbol">(</a><a id="6768" href="Relations.Continuous.html#6768" class="Bound">j</a> <a id="6770" class="Symbol">:</a> <a id="6772" href="Relations.Continuous.html#6658" class="Bound">J</a><a id="6773" class="Symbol">)</a> <a id="6775" class="Symbol">→</a> <a id="6777" href="Relations.Continuous.html#6759" class="Bound">R</a> <a id="6779" class="Symbol">(λ</a> <a id="6782" href="Relations.Continuous.html#6782" class="Bound">i</a> <a id="6784" class="Symbol">→</a> <a id="6786" class="Symbol">(</a><a id="6787" href="Relations.Continuous.html#6761" class="Bound">𝕒</a> <a id="6789" href="Relations.Continuous.html#6782" class="Bound">i</a><a id="6790" class="Symbol">)</a> <a id="6792" href="Relations.Continuous.html#6768" class="Bound">j</a><a id="6793" class="Symbol">)</a>

 <a id="6797" href="Relations.Continuous.html#6797" class="Function">dep-compatible-fun</a> <a id="6816" class="Symbol">:</a> <a id="6818" class="Symbol">(∀</a> <a id="6821" href="Relations.Continuous.html#6821" class="Bound">i</a> <a id="6823" class="Symbol">→</a> <a id="6825" class="Symbol">(</a><a id="6826" href="Relations.Continuous.html#6658" class="Bound">J</a> <a id="6828" class="Symbol">→</a> <a id="6830" href="Relations.Continuous.html#6668" class="Bound">A</a> <a id="6832" href="Relations.Continuous.html#6821" class="Bound">i</a><a id="6833" class="Symbol">)</a> <a id="6835" class="Symbol">→</a> <a id="6837" href="Relations.Continuous.html#6668" class="Bound">A</a> <a id="6839" href="Relations.Continuous.html#6821" class="Bound">i</a><a id="6840" class="Symbol">)</a> <a id="6842" class="Symbol">→</a> <a id="6844" href="Relations.Continuous.html#6045" class="Function">DepRel</a> <a id="6851" href="Relations.Continuous.html#6656" class="Bound">I</a> <a id="6853" href="Relations.Continuous.html#6668" class="Bound">A</a> <a id="6855" href="Relations.Continuous.html#6641" class="Bound">𝓦</a> <a id="6857" class="Symbol">→</a> <a id="6859" href="Relations.Continuous.html#6639" class="Bound">𝓥</a> <a id="6861" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6863" href="Relations.Continuous.html#6637" class="Bound">𝓤</a> <a id="6865" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6867" href="Relations.Continuous.html#6641" class="Bound">𝓦</a> <a id="6869" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6872" href="Relations.Continuous.html#6797" class="Function">dep-compatible-fun</a> <a id="6891" href="Relations.Continuous.html#6891" class="Bound">𝕗</a> <a id="6893" href="Relations.Continuous.html#6893" class="Bound">R</a>  <a id="6896" class="Symbol">=</a> <a id="6898" class="Symbol">∀</a> <a id="6900" href="Relations.Continuous.html#6900" class="Bound">𝕒</a> <a id="6902" class="Symbol">→</a> <a id="6904" class="Symbol">(</a><a id="6905" href="Relations.Continuous.html#6689" class="Function">lift-dep-rel</a> <a id="6918" href="Relations.Continuous.html#6893" class="Bound">R</a><a id="6919" class="Symbol">)</a> <a id="6921" href="Relations.Continuous.html#6900" class="Bound">𝕒</a> <a id="6923" class="Symbol">→</a> <a id="6925" href="Relations.Continuous.html#6893" class="Bound">R</a> <a id="6927" class="Symbol">λ</a> <a id="6929" href="Relations.Continuous.html#6929" class="Bound">i</a> <a id="6931" class="Symbol">→</a> <a id="6933" class="Symbol">(</a><a id="6934" href="Relations.Continuous.html#6891" class="Bound">𝕗</a> <a id="6936" href="Relations.Continuous.html#6929" class="Bound">i</a><a id="6937" class="Symbol">)(</a><a id="6939" href="Relations.Continuous.html#6900" class="Bound">𝕒</a> <a id="6941" href="Relations.Continuous.html#6929" class="Bound">i</a><a id="6942" class="Symbol">)</a>

</pre>

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → J → A i`.


--------------------------------------

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
