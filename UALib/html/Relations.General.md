---
layout: default
title : UALib.Relations.General module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="general-and-dependent-relations">General and Dependent Relations</a>

This section presents the [UALib.Relations.General][] module of the [Agda Universal Algebra Library][].

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `GenRel` to be the type `(I → A) → 𝓦 ̇` and we will call `GenRel` the type of **general relations**.  After that, we define a type that represents relations even more generally.  Specifically, if we are given types `A`, `B`, `C`, etc., we want to represent relations from A to B to C to ….  We define such **dependent relations** [below](Relations.General.html#dependent-relations).

<pre class="Agda">

<a id="1450" class="Symbol">{-#</a> <a id="1454" class="Keyword">OPTIONS</a> <a id="1462" class="Pragma">--without-K</a> <a id="1474" class="Pragma">--exact-split</a> <a id="1488" class="Pragma">--safe</a> <a id="1495" class="Symbol">#-}</a>

<a id="1500" class="Keyword">module</a> <a id="1507" href="Relations.General.html" class="Module">Relations.General</a> <a id="1525" class="Keyword">where</a>

<a id="1532" class="Keyword">open</a> <a id="1537" class="Keyword">import</a> <a id="1544" href="Relations.Binary.html" class="Module">Relations.Binary</a> <a id="1561" class="Keyword">public</a>

</pre>

#### <a id="general-relations">General relations</a>

In this subsection we define the type `GenRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **general relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="GenRel"></a><a id="2168" href="Relations.General.html#2168" class="Function">GenRel</a> <a id="2175" class="Symbol">:</a> <a id="2177" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2179" href="Universes.html#403" class="Function Operator">̇</a> <a id="2181" class="Symbol">→</a> <a id="2183" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2185" href="Universes.html#403" class="Function Operator">̇</a> <a id="2187" class="Symbol">→</a> <a id="2189" class="Symbol">(</a><a id="2190" href="Relations.General.html#2190" class="Bound">𝓦</a> <a id="2192" class="Symbol">:</a> <a id="2194" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2202" class="Symbol">)</a> <a id="2204" class="Symbol">→</a> <a id="2206" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="2208" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2210" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2212" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2214" href="Relations.General.html#2190" class="Bound">𝓦</a> <a id="2216" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="2218" href="Universes.html#403" class="Function Operator">̇</a>
<a id="2220" href="Relations.General.html#2168" class="Function">GenRel</a> <a id="2227" href="Relations.General.html#2227" class="Bound">I</a> <a id="2229" href="Relations.General.html#2229" class="Bound">A</a> <a id="2231" href="Relations.General.html#2231" class="Bound">𝓦</a> <a id="2233" class="Symbol">=</a> <a id="2235" class="Symbol">(</a><a id="2236" href="Relations.General.html#2227" class="Bound">I</a> <a id="2238" class="Symbol">→</a> <a id="2240" href="Relations.General.html#2229" class="Bound">A</a><a id="2241" class="Symbol">)</a> <a id="2243" class="Symbol">→</a> <a id="2245" href="Relations.General.html#2231" class="Bound">𝓦</a> <a id="2247" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with general relations.

<pre class="Agda">

<a id="2497" class="Keyword">module</a> <a id="2504" href="Relations.General.html#2504" class="Module">_</a> <a id="2506" class="Symbol">{</a><a id="2507" href="Relations.General.html#2507" class="Bound">𝓤</a> <a id="2509" href="Relations.General.html#2509" class="Bound">𝓥</a> <a id="2511" href="Relations.General.html#2511" class="Bound">𝓦</a> <a id="2513" class="Symbol">:</a> <a id="2515" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2523" class="Symbol">}</a> <a id="2525" class="Symbol">{</a><a id="2526" href="Relations.General.html#2526" class="Bound">I</a> <a id="2528" href="Relations.General.html#2528" class="Bound">J</a> <a id="2530" class="Symbol">:</a> <a id="2532" href="Relations.General.html#2509" class="Bound">𝓥</a> <a id="2534" href="Universes.html#403" class="Function Operator">̇</a><a id="2535" class="Symbol">}</a> <a id="2537" class="Symbol">{</a><a id="2538" href="Relations.General.html#2538" class="Bound">A</a> <a id="2540" class="Symbol">:</a> <a id="2542" href="Relations.General.html#2507" class="Bound">𝓤</a> <a id="2544" href="Universes.html#403" class="Function Operator">̇</a><a id="2545" class="Symbol">}</a> <a id="2547" class="Keyword">where</a>

 <a id="2555" href="Relations.General.html#2555" class="Function">lift-gen-rel</a> <a id="2568" class="Symbol">:</a> <a id="2570" href="Relations.General.html#2168" class="Function">GenRel</a> <a id="2577" href="Relations.General.html#2526" class="Bound">I</a> <a id="2579" href="Relations.General.html#2538" class="Bound">A</a> <a id="2581" href="Relations.General.html#2511" class="Bound">𝓦</a> <a id="2583" class="Symbol">→</a> <a id="2585" class="Symbol">(</a><a id="2586" href="Relations.General.html#2526" class="Bound">I</a> <a id="2588" class="Symbol">→</a> <a id="2590" class="Symbol">(</a><a id="2591" href="Relations.General.html#2528" class="Bound">J</a> <a id="2593" class="Symbol">→</a> <a id="2595" href="Relations.General.html#2538" class="Bound">A</a><a id="2596" class="Symbol">))</a> <a id="2599" class="Symbol">→</a> <a id="2601" href="Relations.General.html#2509" class="Bound">𝓥</a> <a id="2603" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2605" href="Relations.General.html#2511" class="Bound">𝓦</a> <a id="2607" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2610" href="Relations.General.html#2555" class="Function">lift-gen-rel</a> <a id="2623" href="Relations.General.html#2623" class="Bound">R</a> <a id="2625" href="Relations.General.html#2625" class="Bound">𝕒</a> <a id="2627" class="Symbol">=</a> <a id="2629" class="Symbol">∀</a> <a id="2631" class="Symbol">(</a><a id="2632" href="Relations.General.html#2632" class="Bound">j</a> <a id="2634" class="Symbol">:</a> <a id="2636" href="Relations.General.html#2528" class="Bound">J</a><a id="2637" class="Symbol">)</a> <a id="2639" class="Symbol">→</a> <a id="2641" href="Relations.General.html#2623" class="Bound">R</a> <a id="2643" class="Symbol">(λ</a> <a id="2646" href="Relations.General.html#2646" class="Bound">i</a> <a id="2648" class="Symbol">→</a> <a id="2650" class="Symbol">(</a><a id="2651" href="Relations.General.html#2625" class="Bound">𝕒</a> <a id="2653" href="Relations.General.html#2646" class="Bound">i</a><a id="2654" class="Symbol">)</a> <a id="2656" href="Relations.General.html#2632" class="Bound">j</a><a id="2657" class="Symbol">)</a>

 <a id="2661" href="Relations.General.html#2661" class="Function">gen-compatible-fun</a> <a id="2680" class="Symbol">:</a> <a id="2682" class="Symbol">(</a><a id="2683" href="Relations.General.html#2526" class="Bound">I</a> <a id="2685" class="Symbol">→</a> <a id="2687" class="Symbol">(</a><a id="2688" href="Relations.General.html#2528" class="Bound">J</a> <a id="2690" class="Symbol">→</a> <a id="2692" href="Relations.General.html#2538" class="Bound">A</a><a id="2693" class="Symbol">)</a> <a id="2695" class="Symbol">→</a> <a id="2697" href="Relations.General.html#2538" class="Bound">A</a><a id="2698" class="Symbol">)</a> <a id="2700" class="Symbol">→</a> <a id="2702" href="Relations.General.html#2168" class="Function">GenRel</a> <a id="2709" href="Relations.General.html#2526" class="Bound">I</a> <a id="2711" href="Relations.General.html#2538" class="Bound">A</a> <a id="2713" href="Relations.General.html#2511" class="Bound">𝓦</a> <a id="2715" class="Symbol">→</a> <a id="2717" href="Relations.General.html#2509" class="Bound">𝓥</a> <a id="2719" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2721" href="Relations.General.html#2507" class="Bound">𝓤</a> <a id="2723" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2725" href="Relations.General.html#2511" class="Bound">𝓦</a> <a id="2727" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="2730" href="Relations.General.html#2661" class="Function">gen-compatible-fun</a> <a id="2749" href="Relations.General.html#2749" class="Bound">𝕗</a> <a id="2751" href="Relations.General.html#2751" class="Bound">R</a>  <a id="2754" class="Symbol">=</a> <a id="2756" class="Symbol">∀</a> <a id="2758" href="Relations.General.html#2758" class="Bound">𝕒</a> <a id="2760" class="Symbol">→</a> <a id="2762" class="Symbol">(</a><a id="2763" href="Relations.General.html#2555" class="Function">lift-gen-rel</a> <a id="2776" href="Relations.General.html#2751" class="Bound">R</a><a id="2777" class="Symbol">)</a> <a id="2779" href="Relations.General.html#2758" class="Bound">𝕒</a> <a id="2781" class="Symbol">→</a> <a id="2783" href="Relations.General.html#2751" class="Bound">R</a> <a id="2785" class="Symbol">(λ</a> <a id="2788" href="Relations.General.html#2788" class="Bound">i</a> <a id="2790" class="Symbol">→</a> <a id="2792" class="Symbol">(</a><a id="2793" href="Relations.General.html#2749" class="Bound">𝕗</a> <a id="2795" href="Relations.General.html#2788" class="Bound">i</a><a id="2796" class="Symbol">)</a> <a id="2798" class="Symbol">(</a><a id="2799" href="Relations.General.html#2758" class="Bound">𝕒</a> <a id="2801" href="Relations.General.html#2788" class="Bound">i</a><a id="2802" class="Symbol">))</a>

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

<a id="DepRel"></a><a id="5367" href="Relations.General.html#5367" class="Function">DepRel</a> <a id="5374" class="Symbol">:</a> <a id="5376" class="Symbol">(</a><a id="5377" href="Relations.General.html#5377" class="Bound">I</a> <a id="5379" class="Symbol">:</a> <a id="5381" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="5383" href="Universes.html#403" class="Function Operator">̇</a><a id="5384" class="Symbol">)(</a><a id="5386" href="Relations.General.html#5386" class="Bound">A</a> <a id="5388" class="Symbol">:</a> <a id="5390" href="Relations.General.html#5377" class="Bound">I</a> <a id="5392" class="Symbol">→</a> <a id="5394" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5396" href="Universes.html#403" class="Function Operator">̇</a><a id="5397" class="Symbol">)(</a><a id="5399" href="Relations.General.html#5399" class="Bound">𝓦</a> <a id="5401" class="Symbol">:</a> <a id="5403" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5411" class="Symbol">)</a> <a id="5413" class="Symbol">→</a> <a id="5415" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="5417" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5419" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5421" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5423" href="Relations.General.html#5399" class="Bound">𝓦</a> <a id="5425" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="5427" href="Universes.html#403" class="Function Operator">̇</a>
<a id="5429" href="Relations.General.html#5367" class="Function">DepRel</a> <a id="5436" href="Relations.General.html#5436" class="Bound">I</a> <a id="5438" href="Relations.General.html#5438" class="Bound">A</a> <a id="5440" href="Relations.General.html#5440" class="Bound">𝓦</a> <a id="5442" class="Symbol">=</a> <a id="5444" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5446" href="Relations.General.html#5438" class="Bound">A</a> <a id="5448" class="Symbol">→</a> <a id="5450" href="Relations.General.html#5440" class="Bound">𝓦</a> <a id="5452" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-general-relations">Compatibility with general relations</a>

Above we made peace with lifts of general relations and what it means for such relations to be compatibile with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="5949" class="Keyword">module</a> <a id="5956" href="Relations.General.html#5956" class="Module">_</a> <a id="5958" class="Symbol">{</a><a id="5959" href="Relations.General.html#5959" class="Bound">𝓤</a> <a id="5961" href="Relations.General.html#5961" class="Bound">𝓥</a> <a id="5963" href="Relations.General.html#5963" class="Bound">𝓦</a> <a id="5965" class="Symbol">:</a> <a id="5967" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5975" class="Symbol">}</a> <a id="5977" class="Symbol">{</a><a id="5978" href="Relations.General.html#5978" class="Bound">I</a> <a id="5980" href="Relations.General.html#5980" class="Bound">J</a> <a id="5982" class="Symbol">:</a> <a id="5984" href="Relations.General.html#5961" class="Bound">𝓥</a> <a id="5986" href="Universes.html#403" class="Function Operator">̇</a><a id="5987" class="Symbol">}</a> <a id="5989" class="Symbol">{</a><a id="5990" href="Relations.General.html#5990" class="Bound">A</a> <a id="5992" class="Symbol">:</a> <a id="5994" href="Relations.General.html#5978" class="Bound">I</a> <a id="5996" class="Symbol">→</a> <a id="5998" href="Relations.General.html#5959" class="Bound">𝓤</a> <a id="6000" href="Universes.html#403" class="Function Operator">̇</a><a id="6001" class="Symbol">}</a> <a id="6003" class="Keyword">where</a>

 <a id="6011" href="Relations.General.html#6011" class="Function">lift-dep-rel</a> <a id="6024" class="Symbol">:</a> <a id="6026" href="Relations.General.html#5367" class="Function">DepRel</a> <a id="6033" href="Relations.General.html#5978" class="Bound">I</a> <a id="6035" href="Relations.General.html#5990" class="Bound">A</a> <a id="6037" href="Relations.General.html#5963" class="Bound">𝓦</a> <a id="6039" class="Symbol">→</a> <a id="6041" class="Symbol">((</a><a id="6043" href="Relations.General.html#6043" class="Bound">i</a> <a id="6045" class="Symbol">:</a> <a id="6047" href="Relations.General.html#5978" class="Bound">I</a><a id="6048" class="Symbol">)</a> <a id="6050" class="Symbol">→</a> <a id="6052" class="Symbol">(</a><a id="6053" href="Relations.General.html#5980" class="Bound">J</a> <a id="6055" class="Symbol">→</a> <a id="6057" class="Symbol">(</a><a id="6058" href="Relations.General.html#5990" class="Bound">A</a> <a id="6060" href="Relations.General.html#6043" class="Bound">i</a><a id="6061" class="Symbol">)))</a> <a id="6065" class="Symbol">→</a> <a id="6067" href="Relations.General.html#5961" class="Bound">𝓥</a> <a id="6069" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6071" href="Relations.General.html#5963" class="Bound">𝓦</a> <a id="6073" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6076" href="Relations.General.html#6011" class="Function">lift-dep-rel</a> <a id="6089" href="Relations.General.html#6089" class="Bound">R</a> <a id="6091" href="Relations.General.html#6091" class="Bound">𝕒</a> <a id="6093" class="Symbol">=</a> <a id="6095" class="Symbol">∀</a> <a id="6097" class="Symbol">(</a><a id="6098" href="Relations.General.html#6098" class="Bound">j</a> <a id="6100" class="Symbol">:</a> <a id="6102" href="Relations.General.html#5980" class="Bound">J</a><a id="6103" class="Symbol">)</a> <a id="6105" class="Symbol">→</a> <a id="6107" href="Relations.General.html#6089" class="Bound">R</a> <a id="6109" class="Symbol">(λ</a> <a id="6112" href="Relations.General.html#6112" class="Bound">i</a> <a id="6114" class="Symbol">→</a> <a id="6116" class="Symbol">(</a><a id="6117" href="Relations.General.html#6091" class="Bound">𝕒</a> <a id="6119" href="Relations.General.html#6112" class="Bound">i</a><a id="6120" class="Symbol">)</a> <a id="6122" href="Relations.General.html#6098" class="Bound">j</a><a id="6123" class="Symbol">)</a>

 <a id="6127" href="Relations.General.html#6127" class="Function">dep-compatible-fun</a> <a id="6146" class="Symbol">:</a> <a id="6148" class="Symbol">((</a><a id="6150" href="Relations.General.html#6150" class="Bound">i</a> <a id="6152" class="Symbol">:</a> <a id="6154" href="Relations.General.html#5978" class="Bound">I</a><a id="6155" class="Symbol">)</a> <a id="6157" class="Symbol">→</a> <a id="6159" class="Symbol">(</a><a id="6160" href="Relations.General.html#5980" class="Bound">J</a> <a id="6162" class="Symbol">→</a> <a id="6164" class="Symbol">(</a><a id="6165" href="Relations.General.html#5990" class="Bound">A</a> <a id="6167" href="Relations.General.html#6150" class="Bound">i</a><a id="6168" class="Symbol">))</a> <a id="6171" class="Symbol">→</a> <a id="6173" class="Symbol">(</a><a id="6174" href="Relations.General.html#5990" class="Bound">A</a> <a id="6176" href="Relations.General.html#6150" class="Bound">i</a><a id="6177" class="Symbol">))</a> <a id="6180" class="Symbol">→</a> <a id="6182" href="Relations.General.html#5367" class="Function">DepRel</a> <a id="6189" href="Relations.General.html#5978" class="Bound">I</a> <a id="6191" href="Relations.General.html#5990" class="Bound">A</a> <a id="6193" href="Relations.General.html#5963" class="Bound">𝓦</a> <a id="6195" class="Symbol">→</a> <a id="6197" href="Relations.General.html#5961" class="Bound">𝓥</a> <a id="6199" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6201" href="Relations.General.html#5959" class="Bound">𝓤</a> <a id="6203" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6205" href="Relations.General.html#5963" class="Bound">𝓦</a> <a id="6207" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6210" href="Relations.General.html#6127" class="Function">dep-compatible-fun</a> <a id="6229" href="Relations.General.html#6229" class="Bound">𝕗</a> <a id="6231" href="Relations.General.html#6231" class="Bound">R</a>  <a id="6234" class="Symbol">=</a> <a id="6236" class="Symbol">∀</a> <a id="6238" href="Relations.General.html#6238" class="Bound">𝕒</a> <a id="6240" class="Symbol">→</a> <a id="6242" class="Symbol">(</a><a id="6243" href="Relations.General.html#6011" class="Function">lift-dep-rel</a> <a id="6256" href="Relations.General.html#6231" class="Bound">R</a><a id="6257" class="Symbol">)</a> <a id="6259" href="Relations.General.html#6238" class="Bound">𝕒</a> <a id="6261" class="Symbol">→</a> <a id="6263" href="Relations.General.html#6231" class="Bound">R</a> <a id="6265" class="Symbol">(λ</a> <a id="6268" href="Relations.General.html#6268" class="Bound">i</a> <a id="6270" class="Symbol">→</a> <a id="6272" class="Symbol">(</a><a id="6273" href="Relations.General.html#6229" class="Bound">𝕗</a> <a id="6275" href="Relations.General.html#6268" class="Bound">i</a><a id="6276" class="Symbol">)(</a><a id="6278" href="Relations.General.html#6238" class="Bound">𝕒</a> <a id="6280" href="Relations.General.html#6268" class="Bound">i</a><a id="6281" class="Symbol">))</a>

</pre>

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → (J → (A i))`.


--------------------------------------

[← Relations.Binary](Relations.Binary.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
