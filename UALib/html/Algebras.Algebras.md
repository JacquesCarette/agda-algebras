---
layout: default
title : Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebras">Algebras</a>

This section presents the [Algebras.Algebras][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="280" class="Symbol">{-#</a> <a id="284" class="Keyword">OPTIONS</a> <a id="292" class="Pragma">--without-K</a> <a id="304" class="Pragma">--exact-split</a> <a id="318" class="Pragma">--safe</a> <a id="325" class="Symbol">#-}</a>

<a id="330" class="Keyword">module</a> <a id="337" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="355" class="Keyword">where</a>

<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="394" class="Keyword">public</a>

</pre>


#### <a id="algebra-types">Algebra types</a>

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe `𝓤`, we define the type of *algebras in the signature* 𝑆 (or 𝑆-*algebras*) and with *domain* (or *carrier* or *universe*) `𝐴 : 𝓤 ̇` as follows

<pre class="Agda">

<a id="Algebra"></a><a id="674" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="682" class="Symbol">:</a> <a id="684" class="Symbol">(</a><a id="685" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="687" class="Symbol">:</a> <a id="689" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="697" class="Symbol">)(</a><a id="699" href="Algebras.Algebras.html#699" class="Bound">𝑆</a> <a id="701" class="Symbol">:</a> <a id="703" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="713" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="715" href="Universes.html#262" class="Generalizable">𝓥</a><a id="716" class="Symbol">)</a> <a id="718" class="Symbol">→</a> <a id="720" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="722" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="724" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="726" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="728" href="Algebras.Algebras.html#685" class="Bound">𝓤</a> <a id="730" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="732" href="Universes.html#403" class="Function Operator">̇</a>

<a id="735" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="743" href="Algebras.Algebras.html#743" class="Bound">𝓤</a> <a id="745" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="747" class="Symbol">=</a> <a id="749" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="751" href="Algebras.Algebras.html#751" class="Bound">A</a> <a id="753" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="755" href="Algebras.Algebras.html#743" class="Bound">𝓤</a> <a id="757" href="Universes.html#403" class="Function Operator">̇</a> <a id="759" href="MGS-MLTT.html#3074" class="Function">,</a>                      <a id="782" class="Comment">-- the domain</a>
              <a id="810" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="812" href="Algebras.Algebras.html#812" class="Bound">f</a> <a id="814" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="816" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="818" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="820" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="822" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="824" href="Algebras.Signatures.html#627" class="Function">Op</a> <a id="827" class="Symbol">(</a><a id="828" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="830" href="Algebras.Algebras.html#745" class="Bound">𝑆</a> <a id="832" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="834" href="Algebras.Algebras.html#812" class="Bound">f</a><a id="835" class="Symbol">)</a> <a id="837" href="Algebras.Algebras.html#751" class="Bound">A</a>    <a id="842" class="Comment">-- the basic operations</a>

</pre>

We could refer to an inhabitant of this type as a ∞-*algebra* because its domain can be an arbitrary type, say, `A : 𝓤 ̇` and need not be truncated at some level; in particular, `A` need to be a set. (See the [Overture.Preliminaries.html#truncation](Overture.Preliminaries.html#truncation).)

We might take this opportunity to define the type of 0-*algebras* (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of our algebras are sets in a few places in the [UALib][], so it seems preferable to work with general (∞-)algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.



#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="1858" class="Keyword">record</a> <a id="algebra"></a><a id="1865" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="1873" class="Symbol">(</a><a id="1874" href="Algebras.Algebras.html#1874" class="Bound">𝓤</a> <a id="1876" class="Symbol">:</a> <a id="1878" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1886" class="Symbol">)</a> <a id="1888" class="Symbol">(</a><a id="1889" href="Algebras.Algebras.html#1889" class="Bound">𝑆</a> <a id="1891" class="Symbol">:</a> <a id="1893" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="1903" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="1905" href="Universes.html#262" class="Generalizable">𝓥</a><a id="1906" class="Symbol">)</a> <a id="1908" class="Symbol">:</a> <a id="1910" class="Symbol">(</a><a id="1911" href="Algebras.Algebras.html#1903" class="Bound">𝓞</a> <a id="1913" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1915" href="Algebras.Algebras.html#1905" class="Bound">𝓥</a> <a id="1917" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1919" href="Algebras.Algebras.html#1874" class="Bound">𝓤</a><a id="1920" class="Symbol">)</a> <a id="1922" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1924" href="Universes.html#403" class="Function Operator">̇</a> <a id="1926" class="Keyword">where</a>
 <a id="1933" class="Keyword">constructor</a> <a id="mkalg"></a><a id="1945" href="Algebras.Algebras.html#1945" class="InductiveConstructor">mkalg</a>
 <a id="1952" class="Keyword">field</a>
  <a id="algebra.univ"></a><a id="1960" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="1965" class="Symbol">:</a> <a id="1967" href="Algebras.Algebras.html#1874" class="Bound">𝓤</a> <a id="1969" href="Universes.html#403" class="Function Operator">̇</a>
  <a id="algebra.op"></a><a id="1973" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="1976" class="Symbol">:</a> <a id="1978" class="Symbol">(</a><a id="1979" href="Algebras.Algebras.html#1979" class="Bound">f</a> <a id="1981" class="Symbol">:</a> <a id="1983" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="1985" href="Algebras.Algebras.html#1889" class="Bound">𝑆</a> <a id="1987" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="1988" class="Symbol">)</a> <a id="1990" class="Symbol">→</a> <a id="1992" class="Symbol">((</a><a id="1994" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="1996" href="Algebras.Algebras.html#1889" class="Bound">𝑆</a> <a id="1998" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="2000" href="Algebras.Algebras.html#1979" class="Bound">f</a><a id="2001" class="Symbol">)</a> <a id="2003" class="Symbol">→</a> <a id="2005" href="Algebras.Algebras.html#1960" class="Field">univ</a><a id="2009" class="Symbol">)</a> <a id="2011" class="Symbol">→</a> <a id="2013" href="Algebras.Algebras.html#1960" class="Field">univ</a>


</pre>

Recall, the type `Signature 𝓞 𝓥` was defined in the [Algebras.Signature][] module as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.

If for some reason we want to use both representations of algebras and move back and forth between them, this is easily accomplished with the following functions.

<pre class="Agda">

<a id="2345" class="Keyword">module</a> <a id="2352" href="Algebras.Algebras.html#2352" class="Module">_</a> <a id="2354" class="Symbol">{</a><a id="2355" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="2357" class="Symbol">:</a> <a id="2359" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="2369" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="2371" href="Universes.html#262" class="Generalizable">𝓥</a><a id="2372" class="Symbol">}</a> <a id="2374" class="Keyword">where</a>

 <a id="2382" class="Keyword">open</a> <a id="2387" href="Algebras.Algebras.html#1865" class="Module">algebra</a>

 <a id="2397" href="Algebras.Algebras.html#2397" class="Function">algebra→Algebra</a> <a id="2413" class="Symbol">:</a> <a id="2415" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="2423" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2425" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="2427" class="Symbol">→</a> <a id="2429" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2437" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2439" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a>
 <a id="2442" href="Algebras.Algebras.html#2397" class="Function">algebra→Algebra</a> <a id="2458" href="Algebras.Algebras.html#2458" class="Bound">𝑨</a> <a id="2460" class="Symbol">=</a> <a id="2462" class="Symbol">(</a><a id="2463" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="2468" href="Algebras.Algebras.html#2458" class="Bound">𝑨</a> <a id="2470" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">,</a> <a id="2472" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="2475" href="Algebras.Algebras.html#2458" class="Bound">𝑨</a><a id="2476" class="Symbol">)</a>

 <a id="2480" href="Algebras.Algebras.html#2480" class="Function">Algebra→algebra</a> <a id="2496" class="Symbol">:</a> <a id="2498" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2506" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2508" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="2510" class="Symbol">→</a> <a id="2512" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="2520" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2522" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a>
 <a id="2525" href="Algebras.Algebras.html#2480" class="Function">Algebra→algebra</a> <a id="2541" href="Algebras.Algebras.html#2541" class="Bound">𝑨</a> <a id="2543" class="Symbol">=</a> <a id="2545" href="Algebras.Algebras.html#1945" class="InductiveConstructor">mkalg</a> <a id="2551" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="2553" href="Algebras.Algebras.html#2541" class="Bound">𝑨</a> <a id="2555" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="2557" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="2559" href="Algebras.Algebras.html#2541" class="Bound">𝑨</a> <a id="2561" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a>

</pre>




#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [UALib][].

<pre class="Agda">

 <a id="2989" href="Algebras.Algebras.html#2989" class="Function Operator">_̂_</a> <a id="2993" class="Symbol">:</a> <a id="2995" class="Symbol">(</a><a id="2996" href="Algebras.Algebras.html#2996" class="Bound">𝑓</a> <a id="2998" class="Symbol">:</a> <a id="3000" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="3002" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="3004" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="3005" class="Symbol">)(</a><a id="3007" href="Algebras.Algebras.html#3007" class="Bound">𝑨</a> <a id="3009" class="Symbol">:</a> <a id="3011" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3019" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3021" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a><a id="3022" class="Symbol">)</a> <a id="3024" class="Symbol">→</a> <a id="3026" class="Symbol">(</a><a id="3027" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="3029" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="3031" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="3033" href="Algebras.Algebras.html#2996" class="Bound">𝑓</a>  <a id="3036" class="Symbol">→</a>  <a id="3039" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="3041" href="Algebras.Algebras.html#3007" class="Bound">𝑨</a> <a id="3043" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="3044" class="Symbol">)</a> <a id="3046" class="Symbol">→</a> <a id="3048" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="3050" href="Algebras.Algebras.html#3007" class="Bound">𝑨</a> <a id="3052" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a>

 <a id="3056" href="Algebras.Algebras.html#3056" class="Bound">𝑓</a> <a id="3058" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="3060" href="Algebras.Algebras.html#3060" class="Bound">𝑨</a> <a id="3062" class="Symbol">=</a> <a id="3064" class="Symbol">λ</a> <a id="3066" href="Algebras.Algebras.html#3066" class="Bound">𝑎</a> <a id="3068" class="Symbol">→</a> <a id="3070" class="Symbol">(</a><a id="3071" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="3073" href="Algebras.Algebras.html#3060" class="Bound">𝑨</a> <a id="3075" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="3077" href="Algebras.Algebras.html#3056" class="Bound">𝑓</a><a id="3078" class="Symbol">)</a> <a id="3080" href="Algebras.Algebras.html#3066" class="Bound">𝑎</a>

</pre>

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

We sometimes want to assume that we have at our disposal an arbitrary collection `X` of variable symbols such that, for every algebra `𝑨`, no matter the type of its domain, we have a surjective map of type `X → ∣ 𝑨 ∣`, from variable symbols onto the domain of `𝑨`.  We may use the following definition to express this assumption when we need it.

<pre class="Agda">

 <a id="3759" href="Algebras.Algebras.html#3759" class="Function Operator">_↠_</a> <a id="3763" class="Symbol">:</a> <a id="3765" class="Symbol">{</a><a id="3766" href="Algebras.Algebras.html#3766" class="Bound">𝓧</a> <a id="3768" class="Symbol">:</a> <a id="3770" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3778" class="Symbol">}</a> <a id="3780" class="Symbol">→</a> <a id="3782" href="Algebras.Algebras.html#3766" class="Bound">𝓧</a> <a id="3784" href="Universes.html#403" class="Function Operator">̇</a> <a id="3786" class="Symbol">→</a> <a id="3788" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3796" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3798" href="Algebras.Algebras.html#2355" class="Bound">𝑆</a> <a id="3800" class="Symbol">→</a> <a id="3802" href="Algebras.Algebras.html#3766" class="Bound">𝓧</a> <a id="3804" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3806" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3808" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3811" href="Algebras.Algebras.html#3811" class="Bound">X</a> <a id="3813" href="Algebras.Algebras.html#3759" class="Function Operator">↠</a> <a id="3815" href="Algebras.Algebras.html#3815" class="Bound">𝑨</a> <a id="3817" class="Symbol">=</a> <a id="3819" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3821" href="Algebras.Algebras.html#3821" class="Bound">h</a> <a id="3823" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3825" class="Symbol">(</a><a id="3826" href="Algebras.Algebras.html#3811" class="Bound">X</a> <a id="3828" class="Symbol">→</a> <a id="3830" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="3832" href="Algebras.Algebras.html#3815" class="Bound">𝑨</a> <a id="3834" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="3835" class="Symbol">)</a> <a id="3837" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3839" href="Overture.Inverses.html#2015" class="Function">Epic</a> <a id="3844" href="Algebras.Algebras.html#3821" class="Bound">h</a>

</pre>

Now we can assert, in a specific module, the existence of the surjective map described above by including the following line in that module's declaration, like so.

<pre class="Agda">

<a id="4038" class="Keyword">module</a> <a id="4045" href="Algebras.Algebras.html#4045" class="Module">_</a> <a id="4047" class="Symbol">{</a><a id="4048" href="Algebras.Algebras.html#4048" class="Bound">𝓧</a> <a id="4050" class="Symbol">:</a> <a id="4052" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4060" class="Symbol">}{</a><a id="4062" href="Algebras.Algebras.html#4062" class="Bound">X</a> <a id="4064" class="Symbol">:</a> <a id="4066" href="Algebras.Algebras.html#4048" class="Bound">𝓧</a> <a id="4068" href="Universes.html#403" class="Function Operator">̇</a><a id="4069" class="Symbol">}{</a><a id="4071" href="Algebras.Algebras.html#4071" class="Bound">𝑆</a> <a id="4073" class="Symbol">:</a> <a id="4075" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="4085" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="4087" href="Universes.html#262" class="Generalizable">𝓥</a><a id="4088" class="Symbol">}</a>
         <a id="4099" class="Symbol">{</a><a id="4100" href="Algebras.Algebras.html#4100" class="Bound">𝕏</a> <a id="4102" class="Symbol">:</a> <a id="4104" class="Symbol">(</a><a id="4105" href="Algebras.Algebras.html#4105" class="Bound">𝑨</a> <a id="4107" class="Symbol">:</a> <a id="4109" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4117" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4119" href="Algebras.Algebras.html#4071" class="Bound">𝑆</a><a id="4120" class="Symbol">)</a> <a id="4122" class="Symbol">→</a> <a id="4124" href="Algebras.Algebras.html#4062" class="Bound">X</a> <a id="4126" href="Algebras.Algebras.html#3759" class="Function Operator">↠</a> <a id="4128" href="Algebras.Algebras.html#4105" class="Bound">𝑨</a><a id="4129" class="Symbol">}</a> <a id="4131" class="Keyword">where</a>

</pre>

Then fst(𝕏 𝑨) will denote the surjective map h₀ : X → ∣ 𝑨 ∣, and snd(𝕏 𝑨) will be a proof that h₀ is surjective.




#### <a id="lifts-of-algebras">Level lifting algebra types</a>

Recall, in the [section on level lifting and lowering](Overture.Lifts.html#level-lifting-and-lowering), we described the difficulties one may encounter when working with a noncumulative universe hierarchy. We made a promise to provide some domain-specific level lifting and level lowering methods. Here we fulfill this promise by supplying a couple of bespoke tools designed specifically for our operation and algebra types.

<pre class="Agda">


<a id="4772" class="Keyword">module</a> <a id="4779" href="Algebras.Algebras.html#4779" class="Module">_</a> <a id="4781" class="Symbol">{</a><a id="4782" href="Algebras.Algebras.html#4782" class="Bound">I</a> <a id="4784" class="Symbol">:</a> <a id="4786" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4788" href="Universes.html#403" class="Function Operator">̇</a><a id="4789" class="Symbol">}{</a><a id="4791" href="Algebras.Algebras.html#4791" class="Bound">A</a> <a id="4793" class="Symbol">:</a> <a id="4795" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4797" href="Universes.html#403" class="Function Operator">̇</a><a id="4798" class="Symbol">}</a> <a id="4800" class="Keyword">where</a>

 <a id="4808" class="Keyword">open</a> <a id="4813" href="Overture.Lifts.html#2996" class="Module">Lift</a>

 <a id="4820" href="Algebras.Algebras.html#4820" class="Function">Lift-op</a> <a id="4828" class="Symbol">:</a> <a id="4830" class="Symbol">((</a><a id="4832" href="Algebras.Algebras.html#4782" class="Bound">I</a> <a id="4834" class="Symbol">→</a> <a id="4836" href="Algebras.Algebras.html#4791" class="Bound">A</a><a id="4837" class="Symbol">)</a> <a id="4839" class="Symbol">→</a> <a id="4841" href="Algebras.Algebras.html#4791" class="Bound">A</a><a id="4842" class="Symbol">)</a> <a id="4844" class="Symbol">→</a> <a id="4846" class="Symbol">(</a><a id="4847" href="Algebras.Algebras.html#4847" class="Bound">𝓦</a> <a id="4849" class="Symbol">:</a> <a id="4851" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4859" class="Symbol">)</a> <a id="4861" class="Symbol">→</a> <a id="4863" class="Symbol">((</a><a id="4865" href="Algebras.Algebras.html#4782" class="Bound">I</a> <a id="4867" class="Symbol">→</a> <a id="4869" href="Overture.Lifts.html#2996" class="Record">Lift</a><a id="4873" class="Symbol">{</a><a id="4874" href="Algebras.Algebras.html#4847" class="Bound">𝓦</a><a id="4875" class="Symbol">}</a> <a id="4877" href="Algebras.Algebras.html#4791" class="Bound">A</a><a id="4878" class="Symbol">)</a> <a id="4880" class="Symbol">→</a> <a id="4882" href="Overture.Lifts.html#2996" class="Record">Lift</a> <a id="4887" class="Symbol">{</a><a id="4888" href="Algebras.Algebras.html#4847" class="Bound">𝓦</a><a id="4889" class="Symbol">}</a> <a id="4891" href="Algebras.Algebras.html#4791" class="Bound">A</a><a id="4892" class="Symbol">)</a>
 <a id="4895" href="Algebras.Algebras.html#4820" class="Function">Lift-op</a> <a id="4903" href="Algebras.Algebras.html#4903" class="Bound">f</a> <a id="4905" href="Algebras.Algebras.html#4905" class="Bound">𝓦</a> <a id="4907" class="Symbol">=</a> <a id="4909" class="Symbol">λ</a> <a id="4911" href="Algebras.Algebras.html#4911" class="Bound">x</a> <a id="4913" class="Symbol">→</a> <a id="4915" href="Overture.Lifts.html#3058" class="InductiveConstructor">lift</a> <a id="4920" class="Symbol">(</a><a id="4921" href="Algebras.Algebras.html#4903" class="Bound">f</a> <a id="4923" class="Symbol">(λ</a> <a id="4926" href="Algebras.Algebras.html#4926" class="Bound">i</a> <a id="4928" class="Symbol">→</a> <a id="4930" href="Overture.Lifts.html#3070" class="Field">lower</a> <a id="4936" class="Symbol">(</a><a id="4937" href="Algebras.Algebras.html#4911" class="Bound">x</a> <a id="4939" href="Algebras.Algebras.html#4926" class="Bound">i</a><a id="4940" class="Symbol">)))</a>

<a id="4945" class="Keyword">module</a> <a id="4952" href="Algebras.Algebras.html#4952" class="Module">_</a> <a id="4954" class="Symbol">{</a><a id="4955" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a> <a id="4957" class="Symbol">:</a> <a id="4959" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="4969" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="4971" href="Universes.html#262" class="Generalizable">𝓥</a><a id="4972" class="Symbol">}</a>  <a id="4975" class="Keyword">where</a>

 <a id="4983" class="Keyword">open</a> <a id="4988" href="Algebras.Algebras.html#1865" class="Module">algebra</a>

 <a id="4998" href="Algebras.Algebras.html#4998" class="Function">Lift-alg</a> <a id="5007" class="Symbol">:</a> <a id="5009" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5017" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5019" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a> <a id="5021" class="Symbol">→</a> <a id="5023" class="Symbol">(</a><a id="5024" href="Algebras.Algebras.html#5024" class="Bound">𝓦</a> <a id="5026" class="Symbol">:</a> <a id="5028" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5036" class="Symbol">)</a> <a id="5038" class="Symbol">→</a> <a id="5040" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="5048" class="Symbol">(</a><a id="5049" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5051" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5053" href="Algebras.Algebras.html#5024" class="Bound">𝓦</a><a id="5054" class="Symbol">)</a> <a id="5056" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a>
 <a id="5059" href="Algebras.Algebras.html#4998" class="Function">Lift-alg</a> <a id="5068" href="Algebras.Algebras.html#5068" class="Bound">𝑨</a> <a id="5070" href="Algebras.Algebras.html#5070" class="Bound">𝓦</a> <a id="5072" class="Symbol">=</a> <a id="5074" href="Overture.Lifts.html#2996" class="Record">Lift</a> <a id="5079" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="5081" href="Algebras.Algebras.html#5068" class="Bound">𝑨</a> <a id="5083" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="5085" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">,</a> <a id="5087" class="Symbol">(λ</a> <a id="5090" class="Symbol">(</a><a id="5091" href="Algebras.Algebras.html#5091" class="Bound">𝑓</a> <a id="5093" class="Symbol">:</a> <a id="5095" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="5097" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a> <a id="5099" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="5100" class="Symbol">)</a> <a id="5102" class="Symbol">→</a> <a id="5104" href="Algebras.Algebras.html#4820" class="Function">Lift-op</a> <a id="5112" class="Symbol">(</a><a id="5113" href="Algebras.Algebras.html#5091" class="Bound">𝑓</a> <a id="5115" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="5117" href="Algebras.Algebras.html#5068" class="Bound">𝑨</a><a id="5118" class="Symbol">)</a> <a id="5120" href="Algebras.Algebras.html#5070" class="Bound">𝓦</a><a id="5121" class="Symbol">)</a>

 <a id="5125" href="Algebras.Algebras.html#5125" class="Function">Lift-alg-record-type</a> <a id="5146" class="Symbol">:</a> <a id="5148" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="5156" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5158" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a> <a id="5160" class="Symbol">→</a> <a id="5162" class="Symbol">(</a><a id="5163" href="Algebras.Algebras.html#5163" class="Bound">𝓦</a> <a id="5165" class="Symbol">:</a> <a id="5167" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5175" class="Symbol">)</a> <a id="5177" class="Symbol">→</a> <a id="5179" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="5187" class="Symbol">(</a><a id="5188" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5190" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5192" href="Algebras.Algebras.html#5163" class="Bound">𝓦</a><a id="5193" class="Symbol">)</a> <a id="5195" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a>
 <a id="5198" href="Algebras.Algebras.html#5125" class="Function">Lift-alg-record-type</a> <a id="5219" href="Algebras.Algebras.html#5219" class="Bound">𝑨</a> <a id="5221" href="Algebras.Algebras.html#5221" class="Bound">𝓦</a> <a id="5223" class="Symbol">=</a> <a id="5225" href="Algebras.Algebras.html#1945" class="InductiveConstructor">mkalg</a> <a id="5231" class="Symbol">(</a><a id="5232" href="Overture.Lifts.html#2996" class="Record">Lift</a> <a id="5237" class="Symbol">(</a><a id="5238" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="5243" href="Algebras.Algebras.html#5219" class="Bound">𝑨</a><a id="5244" class="Symbol">))</a> <a id="5247" class="Symbol">(λ</a> <a id="5250" class="Symbol">(</a><a id="5251" href="Algebras.Algebras.html#5251" class="Bound">f</a> <a id="5253" class="Symbol">:</a> <a id="5255" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="5257" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a> <a id="5259" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="5260" class="Symbol">)</a> <a id="5262" class="Symbol">→</a> <a id="5264" href="Algebras.Algebras.html#4820" class="Function">Lift-op</a> <a id="5272" class="Symbol">((</a><a id="5274" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="5277" href="Algebras.Algebras.html#5219" class="Bound">𝑨</a><a id="5278" class="Symbol">)</a> <a id="5280" href="Algebras.Algebras.html#5251" class="Bound">f</a><a id="5281" class="Symbol">)</a> <a id="5283" href="Algebras.Algebras.html#5221" class="Bound">𝓦</a><a id="5284" class="Symbol">)</a>

</pre>

What makes the types just defined useful for resolving type level errors is the nice properties they possess. Specifically, we will prove each of the following properties at various places in the [UALib][].

+ [`Lift` is a homomorphism](Homomorphisms.Basic.html#exmples-of-homomorphisms) (see [Homomorphisms.Basic][])
+ [`Lift` is an "algebraic invariant"](Homomorphisms.Isomorphisms.html#lift-is-an-algebraic-invariant") (see [Homomorphisms.Isomorphisms][])
+ [`Lift` of a subalgebra is a subalgebra](Subalgebras.Subalgebras.html#lifts-of-subalgebras) (see [Subalgebras.Subalgebras][])
+ [`Lift` preserves identities](Varieties.EquationalLogic.html#lift-invariance)) (see [Varieties.EquationalLogic][])


#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

If `𝑨` is an algebra and `R` a binary relation, then `compatible 𝑨 R` will represents the assertion that `R` is *compatible* with all basic operations of `𝑨`. Recall (from [Relations.Discrete][]) that informally this means for every operation symbol `𝑓 : ∣ 𝑆 ∣` and all pairs `u v : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` of tuples from the domain of 𝑨, the following implication holds:

&nbsp;&nbsp; `Π i ꞉ I , R (u i) (u i)` &nbsp;&nbsp;  `→`  &nbsp;&nbsp; `R ((𝑓 ̂ 𝑨) 𝑎) ((𝑓 ̂ 𝑨) 𝑎')`.

In other terms, `∀ 𝑓 → (𝑓 ̂ 𝑨) |: R`. The formal definition of this notion of compatibility is immediate since all the work is done by the relation `|:` (which we already defined in [Relations.Discrete][]).

<pre class="Agda">

 <a id="6782" href="Algebras.Algebras.html#6782" class="Function">compatible</a> <a id="6793" class="Symbol">:</a> <a id="6795" class="Symbol">(</a><a id="6796" href="Algebras.Algebras.html#6796" class="Bound">𝑨</a> <a id="6798" class="Symbol">:</a> <a id="6800" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="6808" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6810" href="Algebras.Algebras.html#4955" class="Bound">𝑆</a><a id="6811" class="Symbol">)</a> <a id="6813" class="Symbol">→</a> <a id="6815" href="Relations.Discrete.html#6780" class="Function">Rel</a> <a id="6819" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="6821" href="Algebras.Algebras.html#6796" class="Bound">𝑨</a> <a id="6823" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="6825" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6827" class="Symbol">→</a> <a id="6829" href="Algebras.Algebras.html#4969" class="Bound">𝓞</a> <a id="6831" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6833" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6835" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6837" href="Algebras.Algebras.html#4971" class="Bound">𝓥</a> <a id="6839" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6841" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6843" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6846" href="Algebras.Algebras.html#6782" class="Function">compatible</a>  <a id="6858" href="Algebras.Algebras.html#6858" class="Bound">𝑨</a> <a id="6860" href="Algebras.Algebras.html#6860" class="Bound">R</a> <a id="6862" class="Symbol">=</a> <a id="6864" class="Symbol">∀</a> <a id="6866" href="Algebras.Algebras.html#6866" class="Bound">𝑓</a> <a id="6868" class="Symbol">→</a> <a id="6870" class="Symbol">(</a><a id="6871" href="Algebras.Algebras.html#6866" class="Bound">𝑓</a> <a id="6873" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="6875" href="Algebras.Algebras.html#6858" class="Bound">𝑨</a><a id="6876" class="Symbol">)</a> <a id="6878" href="Relations.Discrete.html#9896" class="Function Operator">|:</a> <a id="6881" href="Algebras.Algebras.html#6860" class="Bound">R</a>

</pre>

Recall, the `compatible-fun` type was defined in [Relations.Discrete][] module.



---------------------------------------



#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations*</a>

This section presents the `continuous-compatibility` submodule of the [Algebras.Algebras][] module.<sup>[*](Algebras.Algebras.html#fn0)</sup>


Next we define a type that represents *compatibility of a continuous relation* with all operations of an algebra. We start by defining compatibility of a continuous relations with a single operation.

<pre class="Agda">

<a id="7476" class="Keyword">module</a> <a id="continuous-compatibility"></a><a id="7483" href="Algebras.Algebras.html#7483" class="Module">continuous-compatibility</a> <a id="7508" class="Symbol">{</a><a id="7509" href="Algebras.Algebras.html#7509" class="Bound">𝑆</a> <a id="7511" class="Symbol">:</a> <a id="7513" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="7523" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="7525" href="Universes.html#262" class="Generalizable">𝓥</a><a id="7526" class="Symbol">}</a> <a id="7528" class="Symbol">{</a><a id="7529" href="Algebras.Algebras.html#7529" class="Bound">𝑨</a> <a id="7531" class="Symbol">:</a> <a id="7533" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="7541" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7543" href="Algebras.Algebras.html#7509" class="Bound">𝑆</a><a id="7544" class="Symbol">}</a> <a id="7546" class="Symbol">{</a><a id="7547" href="Algebras.Algebras.html#7547" class="Bound">I</a> <a id="7549" class="Symbol">:</a> <a id="7551" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7553" href="Universes.html#403" class="Function Operator">̇</a><a id="7554" class="Symbol">}</a> <a id="7556" class="Keyword">where</a>

 <a id="7564" class="Keyword">open</a> <a id="7569" class="Keyword">import</a> <a id="7576" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="7597" class="Keyword">using</a> <a id="7603" class="Symbol">(</a><a id="7604" href="Relations.Continuous.html#3237" class="Function">ContRel</a><a id="7611" class="Symbol">;</a> <a id="7613" href="Relations.Continuous.html#3860" class="Function">eval-cont-rel</a><a id="7626" class="Symbol">;</a> <a id="7628" href="Relations.Continuous.html#3961" class="Function">cont-compatible-fun</a><a id="7647" class="Symbol">)</a>


 <a id="continuous-compatibility.cont-compatible-op"></a><a id="7652" href="Algebras.Algebras.html#7652" class="Function">cont-compatible-op</a> <a id="7671" class="Symbol">:</a> <a id="7673" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7675" href="Algebras.Algebras.html#7509" class="Bound">𝑆</a> <a id="7677" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7679" class="Symbol">→</a> <a id="7681" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="7689" href="Algebras.Algebras.html#7547" class="Bound">I</a> <a id="7691" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7693" href="Algebras.Algebras.html#7529" class="Bound">𝑨</a> <a id="7695" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7697" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7699" class="Symbol">→</a> <a id="7701" href="Algebras.Algebras.html#7541" class="Bound">𝓤</a> <a id="7703" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7705" href="Algebras.Algebras.html#7525" class="Bound">𝓥</a> <a id="7707" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7709" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7711" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7714" href="Algebras.Algebras.html#7652" class="Function">cont-compatible-op</a> <a id="7733" href="Algebras.Algebras.html#7733" class="Bound">𝑓</a> <a id="7735" href="Algebras.Algebras.html#7735" class="Bound">R</a> <a id="7737" class="Symbol">=</a> <a id="7739" href="Relations.Continuous.html#3961" class="Function">cont-compatible-fun</a> <a id="7759" class="Symbol">(</a><a id="7760" href="Algebras.Algebras.html#7733" class="Bound">𝑓</a> <a id="7762" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="7764" href="Algebras.Algebras.html#7529" class="Bound">𝑨</a><a id="7765" class="Symbol">)</a> <a id="7767" href="Algebras.Algebras.html#7735" class="Bound">R</a>

</pre>

In case it helps the reader understand `con-compatible-op`, we redefine it explicitly without the help of `con-compatible-fun`.

<pre class="Agda">

 <a id="continuous-compatibility.cont-compatible-op&#39;"></a><a id="7926" href="Algebras.Algebras.html#7926" class="Function">cont-compatible-op&#39;</a> <a id="7946" class="Symbol">:</a> <a id="7948" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7950" href="Algebras.Algebras.html#7509" class="Bound">𝑆</a> <a id="7952" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7954" class="Symbol">→</a> <a id="7956" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="7964" href="Algebras.Algebras.html#7547" class="Bound">I</a> <a id="7966" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7968" href="Algebras.Algebras.html#7529" class="Bound">𝑨</a> <a id="7970" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="7972" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7974" class="Symbol">→</a> <a id="7976" href="Algebras.Algebras.html#7541" class="Bound">𝓤</a> <a id="7978" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7980" href="Algebras.Algebras.html#7525" class="Bound">𝓥</a> <a id="7982" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7984" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7986" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7989" href="Algebras.Algebras.html#7926" class="Function">cont-compatible-op&#39;</a> <a id="8009" href="Algebras.Algebras.html#8009" class="Bound">𝑓</a> <a id="8011" href="Algebras.Algebras.html#8011" class="Bound">R</a> <a id="8013" class="Symbol">=</a> <a id="8015" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8017" href="Algebras.Algebras.html#8017" class="Bound">𝒂</a> <a id="8019" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8021" class="Symbol">(</a><a id="8022" href="Algebras.Algebras.html#7547" class="Bound">I</a> <a id="8024" class="Symbol">→</a> <a id="8026" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="8028" href="Algebras.Algebras.html#7509" class="Bound">𝑆</a> <a id="8030" href="Overture.Preliminaries.html#13811" class="Function Operator">∥</a> <a id="8032" href="Algebras.Algebras.html#8009" class="Bound">𝑓</a> <a id="8034" class="Symbol">→</a> <a id="8036" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="8038" href="Algebras.Algebras.html#7529" class="Bound">𝑨</a> <a id="8040" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="8041" class="Symbol">)</a> <a id="8043" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8045" class="Symbol">(</a><a id="8046" href="Relations.Continuous.html#3860" class="Function">eval-cont-rel</a> <a id="8060" href="Algebras.Algebras.html#8011" class="Bound">R</a> <a id="8062" href="Algebras.Algebras.html#8017" class="Bound">𝒂</a> <a id="8064" class="Symbol">→</a> <a id="8066" href="Algebras.Algebras.html#8011" class="Bound">R</a> <a id="8068" class="Symbol">λ</a> <a id="8070" href="Algebras.Algebras.html#8070" class="Bound">i</a> <a id="8072" class="Symbol">→</a> <a id="8074" class="Symbol">(</a><a id="8075" href="Algebras.Algebras.html#8009" class="Bound">𝑓</a> <a id="8077" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="8079" href="Algebras.Algebras.html#7529" class="Bound">𝑨</a><a id="8080" class="Symbol">)(</a><a id="8082" href="Algebras.Algebras.html#8017" class="Bound">𝒂</a> <a id="8084" href="Algebras.Algebras.html#8070" class="Bound">i</a><a id="8085" class="Symbol">))</a>

</pre>

With `cont-compatible-op` in hand, it is a trivial matter to define a type that represents *compatibility of a continuous relation with an algebra*.

<pre class="Agda">

 <a id="continuous-compatibility.cont-compatible"></a><a id="8266" href="Algebras.Algebras.html#8266" class="Function">cont-compatible</a> <a id="8282" class="Symbol">:</a> <a id="8284" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="8292" href="Algebras.Algebras.html#7547" class="Bound">I</a> <a id="8294" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="8296" href="Algebras.Algebras.html#7529" class="Bound">𝑨</a> <a id="8298" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="8300" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8302" class="Symbol">→</a> <a id="8304" href="Algebras.Algebras.html#7523" class="Bound">𝓞</a> <a id="8306" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8308" href="Algebras.Algebras.html#7541" class="Bound">𝓤</a> <a id="8310" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8312" href="Algebras.Algebras.html#7525" class="Bound">𝓥</a> <a id="8314" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8316" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8318" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8321" href="Algebras.Algebras.html#8266" class="Function">cont-compatible</a> <a id="8337" href="Algebras.Algebras.html#8337" class="Bound">R</a> <a id="8339" class="Symbol">=</a> <a id="8341" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8343" href="Algebras.Algebras.html#8343" class="Bound">𝑓</a> <a id="8345" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8347" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="8349" href="Algebras.Algebras.html#7509" class="Bound">𝑆</a> <a id="8351" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="8353" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8355" href="Algebras.Algebras.html#7652" class="Function">cont-compatible-op</a> <a id="8374" href="Algebras.Algebras.html#8343" class="Bound">𝑓</a> <a id="8376" href="Algebras.Algebras.html#8337" class="Bound">R</a>

</pre>



--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<br>
<br>

[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}
