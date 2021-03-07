---
layout: default
title : UALib.Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="big-relations">Continuous Relations</a>

This section presents the [UALib.Relations.Continuous][] module of the [Agda Universal Algebra Library][].

In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `ConRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ConRel` the type of **continuous relations**.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, ternary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type (i.e., they are *single-sorted* relations), but we will remove this limitation as well when we define *dependent continuous relations*.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ConRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types. To be more concrete, given an arbitrary family `A : I → 𝓤 ̇ ` of types, we may have a relation from `A i` to `A i'` to `A i''` to ….  We will refer to such relations as **dependent continuous relations** (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) captures this completely general notion of relation.<sup>[1](Relations.Continuous.html#fn1)</sup>

<pre class="Agda">

<a id="2349" class="Symbol">{-#</a> <a id="2353" class="Keyword">OPTIONS</a> <a id="2361" class="Pragma">--without-K</a> <a id="2373" class="Pragma">--exact-split</a> <a id="2387" class="Pragma">--safe</a> <a id="2394" class="Symbol">#-}</a>

<a id="2399" class="Keyword">module</a> <a id="2406" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="2427" class="Keyword">where</a>

<a id="2434" class="Keyword">open</a> <a id="2439" class="Keyword">import</a> <a id="2446" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="2465" class="Keyword">public</a>

</pre>

#### <a id="continuous-relations">Continuous relations</a>

In this subsection we define the type `ConRel` to represent a predicate or relation of arbitrary arity over a single type `A`. We call this the type of **continuous relations**.

**Notation**. For consistency and readability, throughout the [UALib][] we treat two universe variables with special care.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="ConRel"></a><a id="3081" href="Relations.Continuous.html#3081" class="Function">ConRel</a> <a id="3088" class="Symbol">:</a> <a id="3090" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3092" href="Universes.html#403" class="Function Operator">̇</a> <a id="3094" class="Symbol">→</a> <a id="3096" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3098" href="Universes.html#403" class="Function Operator">̇</a> <a id="3100" class="Symbol">→</a> <a id="3102" class="Symbol">(</a><a id="3103" href="Relations.Continuous.html#3103" class="Bound">𝓦</a> <a id="3105" class="Symbol">:</a> <a id="3107" href="Universes.html#205" class="Postulate">Universe</a><a id="3115" class="Symbol">)</a> <a id="3117" class="Symbol">→</a> <a id="3119" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3121" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3123" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3125" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3127" href="Relations.Continuous.html#3103" class="Bound">𝓦</a> <a id="3129" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="3131" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3133" href="Relations.Continuous.html#3081" class="Function">ConRel</a> <a id="3140" href="Relations.Continuous.html#3140" class="Bound">I</a> <a id="3142" href="Relations.Continuous.html#3142" class="Bound">A</a> <a id="3144" href="Relations.Continuous.html#3144" class="Bound">𝓦</a> <a id="3146" class="Symbol">=</a> <a id="3148" class="Symbol">(</a><a id="3149" href="Relations.Continuous.html#3140" class="Bound">I</a> <a id="3151" class="Symbol">→</a> <a id="3153" href="Relations.Continuous.html#3142" class="Bound">A</a><a id="3154" class="Symbol">)</a> <a id="3156" class="Symbol">→</a> <a id="3158" href="Relations.Continuous.html#3144" class="Bound">𝓦</a> <a id="3160" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


#### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a>

We now define types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.

<pre class="Agda">

<a id="3419" class="Keyword">module</a> <a id="3426" href="Relations.Continuous.html#3426" class="Module">_</a> <a id="3428" class="Symbol">{</a><a id="3429" href="Relations.Continuous.html#3429" class="Bound">𝓤</a> <a id="3431" href="Relations.Continuous.html#3431" class="Bound">𝓥</a> <a id="3433" href="Relations.Continuous.html#3433" class="Bound">𝓦</a> <a id="3435" class="Symbol">:</a> <a id="3437" href="Universes.html#205" class="Postulate">Universe</a><a id="3445" class="Symbol">}</a> <a id="3447" class="Symbol">{</a><a id="3448" href="Relations.Continuous.html#3448" class="Bound">I</a> <a id="3450" href="Relations.Continuous.html#3450" class="Bound">J</a> <a id="3452" class="Symbol">:</a> <a id="3454" href="Relations.Continuous.html#3431" class="Bound">𝓥</a> <a id="3456" href="Universes.html#403" class="Function Operator">̇</a><a id="3457" class="Symbol">}</a> <a id="3459" class="Symbol">{</a><a id="3460" href="Relations.Continuous.html#3460" class="Bound">A</a> <a id="3462" class="Symbol">:</a> <a id="3464" href="Relations.Continuous.html#3429" class="Bound">𝓤</a> <a id="3466" href="Universes.html#403" class="Function Operator">̇</a><a id="3467" class="Symbol">}</a> <a id="3469" class="Keyword">where</a>

 <a id="3477" href="Relations.Continuous.html#3477" class="Function">lift-con-rel</a> <a id="3490" class="Symbol">:</a> <a id="3492" href="Relations.Continuous.html#3081" class="Function">ConRel</a> <a id="3499" href="Relations.Continuous.html#3448" class="Bound">I</a> <a id="3501" href="Relations.Continuous.html#3460" class="Bound">A</a> <a id="3503" href="Relations.Continuous.html#3433" class="Bound">𝓦</a> <a id="3505" class="Symbol">→</a> <a id="3507" class="Symbol">(</a><a id="3508" href="Relations.Continuous.html#3448" class="Bound">I</a> <a id="3510" class="Symbol">→</a> <a id="3512" href="Relations.Continuous.html#3450" class="Bound">J</a> <a id="3514" class="Symbol">→</a> <a id="3516" href="Relations.Continuous.html#3460" class="Bound">A</a><a id="3517" class="Symbol">)</a> <a id="3519" class="Symbol">→</a> <a id="3521" href="Relations.Continuous.html#3431" class="Bound">𝓥</a> <a id="3523" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3525" href="Relations.Continuous.html#3433" class="Bound">𝓦</a> <a id="3527" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3530" href="Relations.Continuous.html#3477" class="Function">lift-con-rel</a> <a id="3543" href="Relations.Continuous.html#3543" class="Bound">R</a> <a id="3545" href="Relations.Continuous.html#3545" class="Bound">𝕒</a> <a id="3547" class="Symbol">=</a> <a id="3549" class="Symbol">∀</a> <a id="3551" class="Symbol">(</a><a id="3552" href="Relations.Continuous.html#3552" class="Bound">j</a> <a id="3554" class="Symbol">:</a> <a id="3556" href="Relations.Continuous.html#3450" class="Bound">J</a><a id="3557" class="Symbol">)</a> <a id="3559" class="Symbol">→</a> <a id="3561" href="Relations.Continuous.html#3543" class="Bound">R</a> <a id="3563" class="Symbol">λ</a> <a id="3565" href="Relations.Continuous.html#3565" class="Bound">i</a> <a id="3567" class="Symbol">→</a> <a id="3569" class="Symbol">(</a><a id="3570" href="Relations.Continuous.html#3545" class="Bound">𝕒</a> <a id="3572" href="Relations.Continuous.html#3565" class="Bound">i</a><a id="3573" class="Symbol">)</a> <a id="3575" href="Relations.Continuous.html#3552" class="Bound">j</a>

 <a id="3579" href="Relations.Continuous.html#3579" class="Function">con-compatible-fun</a> <a id="3598" class="Symbol">:</a> <a id="3600" class="Symbol">(</a><a id="3601" href="Relations.Continuous.html#3448" class="Bound">I</a> <a id="3603" class="Symbol">→</a> <a id="3605" class="Symbol">(</a><a id="3606" href="Relations.Continuous.html#3450" class="Bound">J</a> <a id="3608" class="Symbol">→</a> <a id="3610" href="Relations.Continuous.html#3460" class="Bound">A</a><a id="3611" class="Symbol">)</a> <a id="3613" class="Symbol">→</a> <a id="3615" href="Relations.Continuous.html#3460" class="Bound">A</a><a id="3616" class="Symbol">)</a> <a id="3618" class="Symbol">→</a> <a id="3620" href="Relations.Continuous.html#3081" class="Function">ConRel</a> <a id="3627" href="Relations.Continuous.html#3448" class="Bound">I</a> <a id="3629" href="Relations.Continuous.html#3460" class="Bound">A</a> <a id="3631" href="Relations.Continuous.html#3433" class="Bound">𝓦</a> <a id="3633" class="Symbol">→</a> <a id="3635" href="Relations.Continuous.html#3431" class="Bound">𝓥</a> <a id="3637" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3639" href="Relations.Continuous.html#3429" class="Bound">𝓤</a> <a id="3641" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3643" href="Relations.Continuous.html#3433" class="Bound">𝓦</a> <a id="3645" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3648" href="Relations.Continuous.html#3579" class="Function">con-compatible-fun</a> <a id="3667" href="Relations.Continuous.html#3667" class="Bound">𝕗</a> <a id="3669" href="Relations.Continuous.html#3669" class="Bound">R</a>  <a id="3672" class="Symbol">=</a> <a id="3674" class="Symbol">∀</a> <a id="3676" href="Relations.Continuous.html#3676" class="Bound">𝕒</a> <a id="3678" class="Symbol">→</a> <a id="3680" class="Symbol">(</a><a id="3681" href="Relations.Continuous.html#3477" class="Function">lift-con-rel</a> <a id="3694" href="Relations.Continuous.html#3669" class="Bound">R</a><a id="3695" class="Symbol">)</a> <a id="3697" href="Relations.Continuous.html#3676" class="Bound">𝕒</a> <a id="3699" class="Symbol">→</a> <a id="3701" href="Relations.Continuous.html#3669" class="Bound">R</a> <a id="3703" class="Symbol">λ</a> <a id="3705" href="Relations.Continuous.html#3705" class="Bound">i</a> <a id="3707" class="Symbol">→</a> <a id="3709" class="Symbol">(</a><a id="3710" href="Relations.Continuous.html#3667" class="Bound">𝕗</a> <a id="3712" href="Relations.Continuous.html#3705" class="Bound">i</a><a id="3713" class="Symbol">)</a> <a id="3715" class="Symbol">(</a><a id="3716" href="Relations.Continuous.html#3676" class="Bound">𝕒</a> <a id="3718" href="Relations.Continuous.html#3705" class="Bound">i</a><a id="3719" class="Symbol">)</a>

</pre>

In the definition of `gen-compatible-fun`, we let Agda infer the type of `𝕒`, which is `I → (J → A)`.

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics instead of the semantics.  In fact, we should probably pause here to discuss these semantics, lest the more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝕒 : I → (J → A)` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, recall that a continuous relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Next consider the function `lift-gen-rel`.  For each continuous relation `R`, the type `lift-gen-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝕒 : I → (J → A)` such that `lift-gen-rel R 𝕒` holds.

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

<a id="DepRel"></a><a id="6289" href="Relations.Continuous.html#6289" class="Function">DepRel</a> <a id="6296" class="Symbol">:</a> <a id="6298" class="Symbol">(</a><a id="6299" href="Relations.Continuous.html#6299" class="Bound">I</a> <a id="6301" class="Symbol">:</a> <a id="6303" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6305" href="Universes.html#403" class="Function Operator">̇</a><a id="6306" class="Symbol">)(</a><a id="6308" href="Relations.Continuous.html#6308" class="Bound">A</a> <a id="6310" class="Symbol">:</a> <a id="6312" href="Relations.Continuous.html#6299" class="Bound">I</a> <a id="6314" class="Symbol">→</a> <a id="6316" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6318" href="Universes.html#403" class="Function Operator">̇</a><a id="6319" class="Symbol">)(</a><a id="6321" href="Relations.Continuous.html#6321" class="Bound">𝓦</a> <a id="6323" class="Symbol">:</a> <a id="6325" href="Universes.html#205" class="Postulate">Universe</a><a id="6333" class="Symbol">)</a> <a id="6335" class="Symbol">→</a> <a id="6337" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6339" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6341" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6343" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6345" href="Relations.Continuous.html#6321" class="Bound">𝓦</a> <a id="6347" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="6349" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6351" href="Relations.Continuous.html#6289" class="Function">DepRel</a> <a id="6358" href="Relations.Continuous.html#6358" class="Bound">I</a> <a id="6360" href="Relations.Continuous.html#6360" class="Bound">A</a> <a id="6362" href="Relations.Continuous.html#6362" class="Bound">𝓦</a> <a id="6364" class="Symbol">=</a> <a id="6366" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6368" href="Relations.Continuous.html#6360" class="Bound">A</a> <a id="6370" class="Symbol">→</a> <a id="6372" href="Relations.Continuous.html#6362" class="Bound">𝓦</a> <a id="6374" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of **dependent relations**.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="6877" class="Keyword">module</a> <a id="6884" href="Relations.Continuous.html#6884" class="Module">_</a> <a id="6886" class="Symbol">{</a><a id="6887" href="Relations.Continuous.html#6887" class="Bound">𝓤</a> <a id="6889" href="Relations.Continuous.html#6889" class="Bound">𝓥</a> <a id="6891" href="Relations.Continuous.html#6891" class="Bound">𝓦</a> <a id="6893" class="Symbol">:</a> <a id="6895" href="Universes.html#205" class="Postulate">Universe</a><a id="6903" class="Symbol">}</a> <a id="6905" class="Symbol">{</a><a id="6906" href="Relations.Continuous.html#6906" class="Bound">I</a> <a id="6908" href="Relations.Continuous.html#6908" class="Bound">J</a> <a id="6910" class="Symbol">:</a> <a id="6912" href="Relations.Continuous.html#6889" class="Bound">𝓥</a> <a id="6914" href="Universes.html#403" class="Function Operator">̇</a><a id="6915" class="Symbol">}</a> <a id="6917" class="Symbol">{</a><a id="6918" href="Relations.Continuous.html#6918" class="Bound">A</a> <a id="6920" class="Symbol">:</a> <a id="6922" href="Relations.Continuous.html#6906" class="Bound">I</a> <a id="6924" class="Symbol">→</a> <a id="6926" href="Relations.Continuous.html#6887" class="Bound">𝓤</a> <a id="6928" href="Universes.html#403" class="Function Operator">̇</a><a id="6929" class="Symbol">}</a> <a id="6931" class="Keyword">where</a>

 <a id="6939" href="Relations.Continuous.html#6939" class="Function">lift-dep-rel</a> <a id="6952" class="Symbol">:</a> <a id="6954" href="Relations.Continuous.html#6289" class="Function">DepRel</a> <a id="6961" href="Relations.Continuous.html#6906" class="Bound">I</a> <a id="6963" href="Relations.Continuous.html#6918" class="Bound">A</a> <a id="6965" href="Relations.Continuous.html#6891" class="Bound">𝓦</a> <a id="6967" class="Symbol">→</a> <a id="6969" class="Symbol">(∀</a> <a id="6972" href="Relations.Continuous.html#6972" class="Bound">i</a> <a id="6974" class="Symbol">→</a> <a id="6976" href="Relations.Continuous.html#6908" class="Bound">J</a> <a id="6978" class="Symbol">→</a> <a id="6980" href="Relations.Continuous.html#6918" class="Bound">A</a> <a id="6982" href="Relations.Continuous.html#6972" class="Bound">i</a><a id="6983" class="Symbol">)</a> <a id="6985" class="Symbol">→</a> <a id="6987" href="Relations.Continuous.html#6889" class="Bound">𝓥</a> <a id="6989" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6991" href="Relations.Continuous.html#6891" class="Bound">𝓦</a> <a id="6993" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6996" href="Relations.Continuous.html#6939" class="Function">lift-dep-rel</a> <a id="7009" href="Relations.Continuous.html#7009" class="Bound">R</a> <a id="7011" href="Relations.Continuous.html#7011" class="Bound">𝕒</a> <a id="7013" class="Symbol">=</a> <a id="7015" class="Symbol">∀</a> <a id="7017" class="Symbol">(</a><a id="7018" href="Relations.Continuous.html#7018" class="Bound">j</a> <a id="7020" class="Symbol">:</a> <a id="7022" href="Relations.Continuous.html#6908" class="Bound">J</a><a id="7023" class="Symbol">)</a> <a id="7025" class="Symbol">→</a> <a id="7027" href="Relations.Continuous.html#7009" class="Bound">R</a> <a id="7029" class="Symbol">(λ</a> <a id="7032" href="Relations.Continuous.html#7032" class="Bound">i</a> <a id="7034" class="Symbol">→</a> <a id="7036" class="Symbol">(</a><a id="7037" href="Relations.Continuous.html#7011" class="Bound">𝕒</a> <a id="7039" href="Relations.Continuous.html#7032" class="Bound">i</a><a id="7040" class="Symbol">)</a> <a id="7042" href="Relations.Continuous.html#7018" class="Bound">j</a><a id="7043" class="Symbol">)</a>

 <a id="7047" href="Relations.Continuous.html#7047" class="Function">dep-compatible-fun</a> <a id="7066" class="Symbol">:</a> <a id="7068" class="Symbol">(∀</a> <a id="7071" href="Relations.Continuous.html#7071" class="Bound">i</a> <a id="7073" class="Symbol">→</a> <a id="7075" class="Symbol">(</a><a id="7076" href="Relations.Continuous.html#6908" class="Bound">J</a> <a id="7078" class="Symbol">→</a> <a id="7080" href="Relations.Continuous.html#6918" class="Bound">A</a> <a id="7082" href="Relations.Continuous.html#7071" class="Bound">i</a><a id="7083" class="Symbol">)</a> <a id="7085" class="Symbol">→</a> <a id="7087" href="Relations.Continuous.html#6918" class="Bound">A</a> <a id="7089" href="Relations.Continuous.html#7071" class="Bound">i</a><a id="7090" class="Symbol">)</a> <a id="7092" class="Symbol">→</a> <a id="7094" href="Relations.Continuous.html#6289" class="Function">DepRel</a> <a id="7101" href="Relations.Continuous.html#6906" class="Bound">I</a> <a id="7103" href="Relations.Continuous.html#6918" class="Bound">A</a> <a id="7105" href="Relations.Continuous.html#6891" class="Bound">𝓦</a> <a id="7107" class="Symbol">→</a> <a id="7109" href="Relations.Continuous.html#6889" class="Bound">𝓥</a> <a id="7111" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7113" href="Relations.Continuous.html#6887" class="Bound">𝓤</a> <a id="7115" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7117" href="Relations.Continuous.html#6891" class="Bound">𝓦</a> <a id="7119" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7122" href="Relations.Continuous.html#7047" class="Function">dep-compatible-fun</a> <a id="7141" href="Relations.Continuous.html#7141" class="Bound">𝕗</a> <a id="7143" href="Relations.Continuous.html#7143" class="Bound">R</a>  <a id="7146" class="Symbol">=</a> <a id="7148" class="Symbol">∀</a> <a id="7150" href="Relations.Continuous.html#7150" class="Bound">𝕒</a> <a id="7152" class="Symbol">→</a> <a id="7154" class="Symbol">(</a><a id="7155" href="Relations.Continuous.html#6939" class="Function">lift-dep-rel</a> <a id="7168" href="Relations.Continuous.html#7143" class="Bound">R</a><a id="7169" class="Symbol">)</a> <a id="7171" href="Relations.Continuous.html#7150" class="Bound">𝕒</a> <a id="7173" class="Symbol">→</a> <a id="7175" href="Relations.Continuous.html#7143" class="Bound">R</a> <a id="7177" class="Symbol">λ</a> <a id="7179" href="Relations.Continuous.html#7179" class="Bound">i</a> <a id="7181" class="Symbol">→</a> <a id="7183" class="Symbol">(</a><a id="7184" href="Relations.Continuous.html#7141" class="Bound">𝕗</a> <a id="7186" href="Relations.Continuous.html#7179" class="Bound">i</a><a id="7187" class="Symbol">)(</a><a id="7189" href="Relations.Continuous.html#7150" class="Bound">𝕒</a> <a id="7191" href="Relations.Continuous.html#7179" class="Bound">i</a><a id="7192" class="Symbol">)</a>

</pre>

In the definition of `dep-compatible-fun`, we let Agda infer the type of `𝕒`, which is `(i : I) → J → A i`.


--------------------------------------

<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
