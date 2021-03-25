---
layout: default
title : Relations.Big module (The Agda Universal Algebra Library)
date : 2021-02-28
author: William DeMeo
---

### <a id="continuous-relations">Continuous Relations*</a>

This is the [Relations.Continuous][] module of the [Agda Universal Algebra Library][].<sup>[*](Relations.Continuous.html#fn0)</sup>

<pre class="Agda">

<a id="339" class="Symbol">{-#</a> <a id="343" class="Keyword">OPTIONS</a> <a id="351" class="Pragma">--without-K</a> <a id="363" class="Pragma">--exact-split</a> <a id="377" class="Pragma">--safe</a> <a id="384" class="Symbol">#-}</a>

<a id="389" class="Keyword">module</a> <a id="396" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="417" class="Keyword">where</a>

<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="Relations.Discrete.html" class="Module">Relations.Discrete</a> <a id="455" class="Keyword">public</a>

</pre>

#### <a id="motivation">Motivation</a>
In set theory, an n-ary relation on a set `A` is simply a subset of the n-fold product `A × A × ⋯ × A`.  As such, we could model these as predicates over the type `A × A × ⋯ × A`, or as relations of type `A → A → ⋯ → A → 𝓦 ̇` (for some universe 𝓦).  To implement such a relation in type theory, we would need to know the arity in advance, and then somehow form an n-fold arrow →.  It's easier and more general to instead define an arity type `I : 𝓥 ̇`, and define the type representing `I`-ary relations on `A` as the function type `(I → A) → 𝓦 ̇`.  Then, if we are specifically interested in an n-ary relation for some natural number `n`, we could take `I` to be a finite set (e.g., of type `Fin n`).

Below we will define `ContRel` to be the type `(I → A) → 𝓦 ̇` and we will call `ContRel` the type of *continuous relations*.  This generalizes the discrete relations we defined in [Relations.Discrete] (unary, binary, etc.) since continuous relations can be of arbitrary arity.  They are not completely general, however, since they are defined over a single type. Said another way, they are *single-sorted* relations. We will remove this limitation when we define the type of *dependent continuous relations* at the end of this module.

Just as `Rel A 𝓦` was the single-sorted special case of the multisorted `REL A B 𝓦` type, so too will `ContRel I A 𝓦` be the single-sorted version of a completely general type of relations. The latter will represent relations that not only have arbitrary arities, but also are defined over arbitrary families of types.

To be more concrete, given an arbitrary family `A : I → 𝓤 ̇` of types, we may have a relation from `A i` to `A j` to `A k` to …, where the collection represented by the "indexing" type `I` might not even be enumerable.<sup>[1](Relations.Continuous.html#fn1)</sup>

We refer to such relations as *dependent continuous relations* (or *dependent relations* for short) because the definition of a type that represents them requires depedent types.  The `DepRel` type that we define [below](Relations.Continuous.html#dependent-relations) manifests this completely general notion of relation.

#### <a id="continuous-relations">Continuous relations</a>

We now define the type `ContRel` which represents predicates of arbitrary arity over a single type `A`. We call this the type of *continuous relations*.

**Notation**. For consistency and readability, throughout the [UALib][] we reserve two universe variables for special purposes.  The first of these is 𝓞 which shall be reserved for types that represent *operation symbols* (see [Algebras.Signatures][]). The second is 𝓥 which we reserve for types representing *arities* of relations or operations.

<pre class="Agda">

<a id="ContRel"></a><a id="3237" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="3245" class="Symbol">:</a> <a id="3247" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3249" href="Universes.html#403" class="Function Operator">̇</a> <a id="3251" class="Symbol">→</a> <a id="3253" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3255" href="Universes.html#403" class="Function Operator">̇</a> <a id="3257" class="Symbol">→</a> <a id="3259" class="Symbol">(</a><a id="3260" href="Relations.Continuous.html#3260" class="Bound">𝓦</a> <a id="3262" class="Symbol">:</a> <a id="3264" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3272" class="Symbol">)</a> <a id="3274" class="Symbol">→</a> <a id="3276" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3278" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3280" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3282" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3284" href="Relations.Continuous.html#3260" class="Bound">𝓦</a> <a id="3286" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="3288" href="Universes.html#403" class="Function Operator">̇</a>
<a id="3290" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="3298" href="Relations.Continuous.html#3298" class="Bound">I</a> <a id="3300" href="Relations.Continuous.html#3300" class="Bound">A</a> <a id="3302" href="Relations.Continuous.html#3302" class="Bound">𝓦</a> <a id="3304" class="Symbol">=</a> <a id="3306" class="Symbol">(</a><a id="3307" href="Relations.Continuous.html#3298" class="Bound">I</a> <a id="3309" class="Symbol">→</a> <a id="3311" href="Relations.Continuous.html#3300" class="Bound">A</a><a id="3312" class="Symbol">)</a> <a id="3314" class="Symbol">→</a> <a id="3316" href="Relations.Continuous.html#3302" class="Bound">𝓦</a> <a id="3318" href="Universes.html#403" class="Function Operator">̇</a>

</pre>


<!-- #### <a id="compatibility-with-continuous-relations">Compatibility with continuous relations</a> -->

Next we present types that are useful for asserting and proving facts about *compatibility* of functions with continuous relations.  The first is an *evaluation* function which "lifts" an `I`-ary relation to an `I → J`-ary relation. The lifted relation will relate a collection of `I` `J`-tuples when their "`I`-slices" (or "rows") belong to the original relation.

<pre class="Agda">

<a id="3821" class="Keyword">module</a> <a id="3828" href="Relations.Continuous.html#3828" class="Module">_</a> <a id="3830" class="Symbol">{</a><a id="3831" href="Relations.Continuous.html#3831" class="Bound">I</a> <a id="3833" href="Relations.Continuous.html#3833" class="Bound">J</a> <a id="3835" class="Symbol">:</a> <a id="3837" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="3839" href="Universes.html#403" class="Function Operator">̇</a><a id="3840" class="Symbol">}</a> <a id="3842" class="Symbol">{</a><a id="3843" href="Relations.Continuous.html#3843" class="Bound">A</a> <a id="3845" class="Symbol">:</a> <a id="3847" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3849" href="Universes.html#403" class="Function Operator">̇</a><a id="3850" class="Symbol">}</a> <a id="3852" class="Keyword">where</a>

 <a id="3860" href="Relations.Continuous.html#3860" class="Function">eval-cont-rel</a> <a id="3874" class="Symbol">:</a> <a id="3876" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="3884" href="Relations.Continuous.html#3831" class="Bound">I</a> <a id="3886" href="Relations.Continuous.html#3843" class="Bound">A</a> <a id="3888" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3890" class="Symbol">→</a> <a id="3892" class="Symbol">(</a><a id="3893" href="Relations.Continuous.html#3831" class="Bound">I</a> <a id="3895" class="Symbol">→</a> <a id="3897" href="Relations.Continuous.html#3833" class="Bound">J</a> <a id="3899" class="Symbol">→</a> <a id="3901" href="Relations.Continuous.html#3843" class="Bound">A</a><a id="3902" class="Symbol">)</a> <a id="3904" class="Symbol">→</a> <a id="3906" href="Relations.Continuous.html#3837" class="Bound">𝓥</a> <a id="3908" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3910" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="3912" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3915" href="Relations.Continuous.html#3860" class="Function">eval-cont-rel</a> <a id="3929" href="Relations.Continuous.html#3929" class="Bound">R</a> <a id="3931" href="Relations.Continuous.html#3931" class="Bound">𝒂</a> <a id="3933" class="Symbol">=</a> <a id="3935" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="3937" href="Relations.Continuous.html#3937" class="Bound">j</a> <a id="3939" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="3941" href="Relations.Continuous.html#3833" class="Bound">J</a> <a id="3943" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="3945" href="Relations.Continuous.html#3929" class="Bound">R</a> <a id="3947" class="Symbol">λ</a> <a id="3949" href="Relations.Continuous.html#3949" class="Bound">i</a> <a id="3951" class="Symbol">→</a> <a id="3953" href="Relations.Continuous.html#3931" class="Bound">𝒂</a> <a id="3955" href="Relations.Continuous.html#3949" class="Bound">i</a> <a id="3957" href="Relations.Continuous.html#3937" class="Bound">j</a>

 <a id="3961" href="Relations.Continuous.html#3961" class="Function">cont-compatible-fun</a> <a id="3981" class="Symbol">:</a> <a id="3983" class="Symbol">((</a><a id="3985" href="Relations.Continuous.html#3833" class="Bound">J</a> <a id="3987" class="Symbol">→</a> <a id="3989" href="Relations.Continuous.html#3843" class="Bound">A</a><a id="3990" class="Symbol">)</a> <a id="3992" class="Symbol">→</a> <a id="3994" href="Relations.Continuous.html#3843" class="Bound">A</a><a id="3995" class="Symbol">)</a> <a id="3997" class="Symbol">→</a> <a id="3999" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="4007" href="Relations.Continuous.html#3831" class="Bound">I</a> <a id="4009" href="Relations.Continuous.html#3843" class="Bound">A</a> <a id="4011" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4013" class="Symbol">→</a> <a id="4015" href="Relations.Continuous.html#3837" class="Bound">𝓥</a> <a id="4017" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4019" href="Relations.Continuous.html#3847" class="Bound">𝓤</a> <a id="4021" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4023" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="4025" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4028" href="Relations.Continuous.html#3961" class="Function">cont-compatible-fun</a> <a id="4048" href="Relations.Continuous.html#4048" class="Bound">𝑓</a> <a id="4050" href="Relations.Continuous.html#4050" class="Bound">R</a>  <a id="4053" class="Symbol">=</a> <a id="4055" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="4057" href="Relations.Continuous.html#4057" class="Bound">𝒂</a> <a id="4059" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="4061" class="Symbol">(</a><a id="4062" href="Relations.Continuous.html#3831" class="Bound">I</a> <a id="4064" class="Symbol">→</a> <a id="4066" href="Relations.Continuous.html#3833" class="Bound">J</a> <a id="4068" class="Symbol">→</a> <a id="4070" href="Relations.Continuous.html#3843" class="Bound">A</a><a id="4071" class="Symbol">)</a> <a id="4073" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="4075" class="Symbol">(</a><a id="4076" href="Relations.Continuous.html#3860" class="Function">eval-cont-rel</a> <a id="4090" href="Relations.Continuous.html#4050" class="Bound">R</a> <a id="4092" href="Relations.Continuous.html#4057" class="Bound">𝒂</a> <a id="4094" class="Symbol">→</a> <a id="4096" href="Relations.Continuous.html#4050" class="Bound">R</a> <a id="4098" class="Symbol">λ</a> <a id="4100" href="Relations.Continuous.html#4100" class="Bound">i</a> <a id="4102" class="Symbol">→</a> <a id="4104" class="Symbol">(</a><a id="4105" href="Relations.Continuous.html#4048" class="Bound">𝑓</a> <a id="4107" class="Symbol">(</a><a id="4108" href="Relations.Continuous.html#4057" class="Bound">𝒂</a> <a id="4110" href="Relations.Continuous.html#4100" class="Bound">i</a><a id="4111" class="Symbol">)))</a>

</pre>

If the syntax of the last two definitions makes you feel a bit nauseated, we recommend focusing on the semantics. In fact, we should probably pause here to discuss these semantics, lest the even more complicated definitions below induce the typical consequence of nausea.

First, internalize the fact that `𝒂 : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Once that's obvious, then recall that a continuous relation `R` represents a certain collection of `I`-tuples. Specifically, if `x : I → A` is an `I`-tuple, then `R x` denotes the assertion that "`x` belongs to `R`" or "`x` satisfies `R`."

Now consider the function `eval-cont-rel`.  For each continuous relation `R`, the type `eval-cont-rel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the `𝒂 : I → J → A` such that `eval-cont-rel R 𝒂` holds.

It helps to visualize such `J`-tuples as columns and imagine for simplicity that `J` is a finite set, say, `{1, 2, ..., J}`.  Picture a couple of these columns, say, the i-th and k-th, like so.

```
𝒂 i 1      𝒂 k 1
𝒂 i 2      𝒂 k 2
𝑎 i 3      𝒂 k 3    <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
𝒂 i J      𝒂 k J
```

Now `eval-cont-rel R 𝒂` is defined by `∀ j → R (λ i → 𝒂 i j)` which represents the assertion that each row of the `I` columns shown above (which evidently is an `I`-tuple) belongs to the original relation `R`.

Next, let's dissect the definition of `cont-compatible-fun`.  Here, `𝑓 : (J → A) → A` denotes a `J`-ary operation on `A`.  That is, `𝑓` takes a `J`-tuple `𝒂 i : J → A` and evaluates to some inhabitant `𝑓 (𝑎 i) : A`.

Finally, digest all the types involved in these definitions and note how nicely they align (as they must if type-checking is to succeed!).  For example, `𝒂 : I → (J → A)` is precisely the type on which the relation `eval-cont-rel R` is defined.


#### <a id="dependent-relations">Dependent relations</a>

In this section we exploit the power of dependent types to define a completely general relation type.  Specifically, we let the tuples inhabit a dependent function type `𝒜 : I → 𝓤 ̇`, where the codomain may depend upon the input coordinate `i : I` of the domain. Heuristically, think of the inhabitants of the following type as relations from `𝒜 i` to `𝒜 j` to `𝒜 k` to ….

<pre class="Agda">

<a id="DepRel"></a><a id="6439" href="Relations.Continuous.html#6439" class="Function">DepRel</a> <a id="6446" class="Symbol">:</a> <a id="6448" class="Symbol">(</a><a id="6449" href="Relations.Continuous.html#6449" class="Bound">I</a> <a id="6451" class="Symbol">:</a> <a id="6453" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6455" href="Universes.html#403" class="Function Operator">̇</a><a id="6456" class="Symbol">)</a> <a id="6458" class="Symbol">→</a> <a id="6460" class="Symbol">(</a><a id="6461" href="Relations.Continuous.html#6449" class="Bound">I</a> <a id="6463" class="Symbol">→</a> <a id="6465" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6467" href="Universes.html#403" class="Function Operator">̇</a><a id="6468" class="Symbol">)</a> <a id="6470" class="Symbol">→</a> <a id="6472" class="Symbol">(</a><a id="6473" href="Relations.Continuous.html#6473" class="Bound">𝓦</a> <a id="6475" class="Symbol">:</a> <a id="6477" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="6485" class="Symbol">)</a> <a id="6487" class="Symbol">→</a> <a id="6489" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="6491" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6493" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6495" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6497" href="Relations.Continuous.html#6473" class="Bound">𝓦</a> <a id="6499" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="6501" href="Universes.html#403" class="Function Operator">̇</a>
<a id="6503" href="Relations.Continuous.html#6439" class="Function">DepRel</a> <a id="6510" href="Relations.Continuous.html#6510" class="Bound">I</a> <a id="6512" href="Relations.Continuous.html#6512" class="Bound">𝒜</a> <a id="6514" href="Relations.Continuous.html#6514" class="Bound">𝓦</a> <a id="6516" class="Symbol">=</a> <a id="6518" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="6520" href="Relations.Continuous.html#6512" class="Bound">𝒜</a> <a id="6522" class="Symbol">→</a> <a id="6524" href="Relations.Continuous.html#6514" class="Bound">𝓦</a> <a id="6526" href="Universes.html#403" class="Function Operator">̇</a>

</pre>

We call `DepRel` the type of *dependent relations*.

#### <a id="compatibility-with-dependent-relations">Compatibility with dependent relations</a>

Above we made peace with lifts of continuous relations and what it means for such relations to be compatible with functions, we conclude this module by defining the (only slightly more complicated) lift of dependent relations, and the type that represents compatibility of a tuple of operations with a dependent relation.

<pre class="Agda">

<a id="7027" class="Keyword">module</a> <a id="7034" href="Relations.Continuous.html#7034" class="Module">_</a> <a id="7036" class="Symbol">{</a><a id="7037" href="Relations.Continuous.html#7037" class="Bound">I</a> <a id="7039" href="Relations.Continuous.html#7039" class="Bound">J</a> <a id="7041" class="Symbol">:</a> <a id="7043" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7045" href="Universes.html#403" class="Function Operator">̇</a><a id="7046" class="Symbol">}</a> <a id="7048" class="Symbol">{</a><a id="7049" href="Relations.Continuous.html#7049" class="Bound">𝒜</a> <a id="7051" class="Symbol">:</a> <a id="7053" href="Relations.Continuous.html#7037" class="Bound">I</a> <a id="7055" class="Symbol">→</a> <a id="7057" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7059" href="Universes.html#403" class="Function Operator">̇</a><a id="7060" class="Symbol">}</a> <a id="7062" class="Keyword">where</a>

 <a id="7070" href="Relations.Continuous.html#7070" class="Function">lift-dep-rel</a> <a id="7083" class="Symbol">:</a> <a id="7085" href="Relations.Continuous.html#6439" class="Function">DepRel</a> <a id="7092" href="Relations.Continuous.html#7037" class="Bound">I</a> <a id="7094" href="Relations.Continuous.html#7049" class="Bound">𝒜</a> <a id="7096" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7098" class="Symbol">→</a> <a id="7100" class="Symbol">(∀</a> <a id="7103" href="Relations.Continuous.html#7103" class="Bound">i</a> <a id="7105" class="Symbol">→</a> <a id="7107" href="Relations.Continuous.html#7039" class="Bound">J</a> <a id="7109" class="Symbol">→</a> <a id="7111" href="Relations.Continuous.html#7049" class="Bound">𝒜</a> <a id="7113" href="Relations.Continuous.html#7103" class="Bound">i</a><a id="7114" class="Symbol">)</a> <a id="7116" class="Symbol">→</a> <a id="7118" href="Relations.Continuous.html#7043" class="Bound">𝓥</a> <a id="7120" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7122" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7124" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7127" href="Relations.Continuous.html#7070" class="Function">lift-dep-rel</a> <a id="7140" href="Relations.Continuous.html#7140" class="Bound">R</a> <a id="7142" href="Relations.Continuous.html#7142" class="Bound">𝕒</a> <a id="7144" class="Symbol">=</a> <a id="7146" class="Symbol">∀</a> <a id="7148" class="Symbol">(</a><a id="7149" href="Relations.Continuous.html#7149" class="Bound">j</a> <a id="7151" class="Symbol">:</a> <a id="7153" href="Relations.Continuous.html#7039" class="Bound">J</a><a id="7154" class="Symbol">)</a> <a id="7156" class="Symbol">→</a> <a id="7158" href="Relations.Continuous.html#7140" class="Bound">R</a> <a id="7160" class="Symbol">(λ</a> <a id="7163" href="Relations.Continuous.html#7163" class="Bound">i</a> <a id="7165" class="Symbol">→</a> <a id="7167" class="Symbol">(</a><a id="7168" href="Relations.Continuous.html#7142" class="Bound">𝕒</a> <a id="7170" href="Relations.Continuous.html#7163" class="Bound">i</a><a id="7171" class="Symbol">)</a> <a id="7173" href="Relations.Continuous.html#7149" class="Bound">j</a><a id="7174" class="Symbol">)</a>

 <a id="7178" href="Relations.Continuous.html#7178" class="Function">dep-compatible-fun</a> <a id="7197" class="Symbol">:</a> <a id="7199" class="Symbol">(∀</a> <a id="7202" href="Relations.Continuous.html#7202" class="Bound">i</a> <a id="7204" class="Symbol">→</a> <a id="7206" class="Symbol">(</a><a id="7207" href="Relations.Continuous.html#7039" class="Bound">J</a> <a id="7209" class="Symbol">→</a> <a id="7211" href="Relations.Continuous.html#7049" class="Bound">𝒜</a> <a id="7213" href="Relations.Continuous.html#7202" class="Bound">i</a><a id="7214" class="Symbol">)</a> <a id="7216" class="Symbol">→</a> <a id="7218" href="Relations.Continuous.html#7049" class="Bound">𝒜</a> <a id="7220" href="Relations.Continuous.html#7202" class="Bound">i</a><a id="7221" class="Symbol">)</a> <a id="7223" class="Symbol">→</a> <a id="7225" href="Relations.Continuous.html#6439" class="Function">DepRel</a> <a id="7232" href="Relations.Continuous.html#7037" class="Bound">I</a> <a id="7234" href="Relations.Continuous.html#7049" class="Bound">𝒜</a> <a id="7236" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7238" class="Symbol">→</a> <a id="7240" href="Relations.Continuous.html#7043" class="Bound">𝓥</a> <a id="7242" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7244" href="Relations.Continuous.html#7057" class="Bound">𝓤</a> <a id="7246" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7248" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7250" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7253" href="Relations.Continuous.html#7178" class="Function">dep-compatible-fun</a> <a id="7272" href="Relations.Continuous.html#7272" class="Bound">𝕗</a> <a id="7274" href="Relations.Continuous.html#7274" class="Bound">R</a>  <a id="7277" class="Symbol">=</a> <a id="7279" class="Symbol">∀</a> <a id="7281" href="Relations.Continuous.html#7281" class="Bound">𝕒</a> <a id="7283" class="Symbol">→</a> <a id="7285" class="Symbol">(</a><a id="7286" href="Relations.Continuous.html#7070" class="Function">lift-dep-rel</a> <a id="7299" href="Relations.Continuous.html#7274" class="Bound">R</a><a id="7300" class="Symbol">)</a> <a id="7302" href="Relations.Continuous.html#7281" class="Bound">𝕒</a> <a id="7304" class="Symbol">→</a> <a id="7306" href="Relations.Continuous.html#7274" class="Bound">R</a> <a id="7308" class="Symbol">λ</a> <a id="7310" href="Relations.Continuous.html#7310" class="Bound">i</a> <a id="7312" class="Symbol">→</a> <a id="7314" class="Symbol">(</a><a id="7315" href="Relations.Continuous.html#7272" class="Bound">𝕗</a> <a id="7317" href="Relations.Continuous.html#7310" class="Bound">i</a><a id="7318" class="Symbol">)(</a><a id="7320" href="Relations.Continuous.html#7281" class="Bound">𝕒</a> <a id="7322" href="Relations.Continuous.html#7310" class="Bound">i</a><a id="7323" class="Symbol">)</a>

</pre>

(In the definition of `dep-compatible-fun`, we let Agda infer the type `(i : I) → J → 𝒜 i` of `𝕒`.)


--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<sup>[1]</sup><span class="footnote" id="fn1"> Because the collection represented by the indexing type `I` might not even be enumerable, technically speaking, instead of `A i` to `A j` to `A k` to ..., we should have written something like `TO (i : I) , A i`.</span>


<p></p>

[← Relations.Discrete](Relations.Discrete.html)
<span style="float:right;">[Relations.Quotients →](Relations.Quotients.html)</span>

{% include UALib.Links.md %}
