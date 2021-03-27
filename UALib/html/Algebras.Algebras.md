---
layout: default
title : Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

\section{Algebras}\label{algebras}

This section presents the \href{Algebras.Algebras.html}{Algebras.Algebras} module of the \href{https://gitlab.com/ualib/ualib.gitlab.io/}{Agda Universal Algebra Library}.

<pre class="Agda">

<a id="354" class="Symbol">{-#</a> <a id="358" class="Keyword">OPTIONS</a> <a id="366" class="Pragma">--without-K</a> <a id="378" class="Pragma">--exact-split</a> <a id="392" class="Pragma">--safe</a> <a id="399" class="Symbol">#-}</a>

<a id="404" class="Keyword">module</a> <a id="411" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="429" class="Keyword">where</a>

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="468" class="Keyword">public</a>

</pre>


\subsection{Algebra types}\label{algebra-types}

For a fixed signature \AgdaBound{𝑆} : \AgdaFunction{Signature} 𝓞 𝓥` and universe `𝓤`, we define the type of *algebras in the signature* 𝑆 (or 𝑆-*algebras*) and with *domain* (or *carrier* or *universe*) `𝐴 : 𝓤 ̇` as follows

<pre class="Agda">

<a id="Algebra"></a><a id="777" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="785" class="Symbol">:</a> <a id="787" class="Symbol">(</a><a id="788" href="Algebras.Algebras.html#788" class="Bound">𝓤</a> <a id="790" class="Symbol">:</a> <a id="792" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="800" class="Symbol">)(</a><a id="802" href="Algebras.Algebras.html#802" class="Bound">𝑆</a> <a id="804" class="Symbol">:</a> <a id="806" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="816" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="818" href="Universes.html#262" class="Generalizable">𝓥</a><a id="819" class="Symbol">)</a> <a id="821" class="Symbol">→</a> <a id="823" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="825" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="827" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="829" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="831" href="Algebras.Algebras.html#788" class="Bound">𝓤</a> <a id="833" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="835" href="Universes.html#403" class="Function Operator">̇</a>

<a id="838" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="846" href="Algebras.Algebras.html#846" class="Bound">𝓤</a> <a id="848" href="Algebras.Algebras.html#848" class="Bound">𝑆</a> <a id="850" class="Symbol">=</a> <a id="852" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="854" href="Algebras.Algebras.html#854" class="Bound">A</a> <a id="856" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="858" href="Algebras.Algebras.html#846" class="Bound">𝓤</a> <a id="860" href="Universes.html#403" class="Function Operator">̇</a> <a id="862" href="MGS-MLTT.html#3074" class="Function">,</a>                      <a id="885" class="Comment">-- the domain</a>
              <a id="913" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="915" href="Algebras.Algebras.html#915" class="Bound">f</a> <a id="917" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="919" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="921" href="Algebras.Algebras.html#848" class="Bound">𝑆</a> <a id="923" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="925" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="927" href="Algebras.Signatures.html#727" class="Function">Op</a> <a id="930" class="Symbol">(</a><a id="931" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="933" href="Algebras.Algebras.html#848" class="Bound">𝑆</a> <a id="935" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="937" href="Algebras.Algebras.html#915" class="Bound">f</a><a id="938" class="Symbol">)</a> <a id="940" href="Algebras.Algebras.html#854" class="Bound">A</a>    <a id="945" class="Comment">-- the basic operations</a>

</pre>

We could refer to an inhabitant of this type as a ∞-*algebra* because its domain can be an arbitrary type, say, `A : 𝓤 ̇` and need not be truncated at some level; in particular, `A` need to be a set. (See the [Overture.Preliminaries.html#truncation](Overture.Preliminaries.html#truncation).)

We might take this opportunity to define the type of 0-*algebras* (algebras whose domains are sets), which is probably closer to what most of us think of when doing informal universal algebra.  However, below we will only need to know that the domains of our algebras are sets in a few places in the [UALib][], so it seems preferable to work with general (∞-)algebras throughout and then assume uniquness of identity proofs explicitly and only where needed.



#### <a id="algebras-as-record-types">Algebras as record types</a>

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

<pre class="Agda">

<a id="1961" class="Keyword">record</a> <a id="algebra"></a><a id="1968" href="Algebras.Algebras.html#1968" class="Record">algebra</a> <a id="1976" class="Symbol">(</a><a id="1977" href="Algebras.Algebras.html#1977" class="Bound">𝓤</a> <a id="1979" class="Symbol">:</a> <a id="1981" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1989" class="Symbol">)</a> <a id="1991" class="Symbol">(</a><a id="1992" href="Algebras.Algebras.html#1992" class="Bound">𝑆</a> <a id="1994" class="Symbol">:</a> <a id="1996" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="2006" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="2008" href="Universes.html#262" class="Generalizable">𝓥</a><a id="2009" class="Symbol">)</a> <a id="2011" class="Symbol">:</a> <a id="2013" class="Symbol">(</a><a id="2014" href="Algebras.Algebras.html#2006" class="Bound">𝓞</a> <a id="2016" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2018" href="Algebras.Algebras.html#2008" class="Bound">𝓥</a> <a id="2020" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2022" href="Algebras.Algebras.html#1977" class="Bound">𝓤</a><a id="2023" class="Symbol">)</a> <a id="2025" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="2027" href="Universes.html#403" class="Function Operator">̇</a> <a id="2029" class="Keyword">where</a>
 <a id="2036" class="Keyword">constructor</a> <a id="mkalg"></a><a id="2048" href="Algebras.Algebras.html#2048" class="InductiveConstructor">mkalg</a>
 <a id="2055" class="Keyword">field</a>
  <a id="algebra.univ"></a><a id="2063" href="Algebras.Algebras.html#2063" class="Field">univ</a> <a id="2068" class="Symbol">:</a> <a id="2070" href="Algebras.Algebras.html#1977" class="Bound">𝓤</a> <a id="2072" href="Universes.html#403" class="Function Operator">̇</a>
  <a id="algebra.op"></a><a id="2076" href="Algebras.Algebras.html#2076" class="Field">op</a> <a id="2079" class="Symbol">:</a> <a id="2081" class="Symbol">(</a><a id="2082" href="Algebras.Algebras.html#2082" class="Bound">f</a> <a id="2084" class="Symbol">:</a> <a id="2086" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="2088" href="Algebras.Algebras.html#1992" class="Bound">𝑆</a> <a id="2090" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a><a id="2091" class="Symbol">)</a> <a id="2093" class="Symbol">→</a> <a id="2095" class="Symbol">((</a><a id="2097" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="2099" href="Algebras.Algebras.html#1992" class="Bound">𝑆</a> <a id="2101" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="2103" href="Algebras.Algebras.html#2082" class="Bound">f</a><a id="2104" class="Symbol">)</a> <a id="2106" class="Symbol">→</a> <a id="2108" href="Algebras.Algebras.html#2063" class="Field">univ</a><a id="2112" class="Symbol">)</a> <a id="2114" class="Symbol">→</a> <a id="2116" href="Algebras.Algebras.html#2063" class="Field">univ</a>


</pre>

Recall, the type `Signature 𝓞 𝓥` was defined in the [Algebras.Signature][] module as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.

If for some reason we want to use both representations of algebras and move back and forth between them, this is easily accomplished with the following functions.

<pre class="Agda">

<a id="2448" class="Keyword">module</a> <a id="2455" href="Algebras.Algebras.html#2455" class="Module">_</a> <a id="2457" class="Symbol">{</a><a id="2458" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="2460" class="Symbol">:</a> <a id="2462" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="2472" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="2474" href="Universes.html#262" class="Generalizable">𝓥</a><a id="2475" class="Symbol">}</a> <a id="2477" class="Keyword">where</a>

 <a id="2485" class="Keyword">open</a> <a id="2490" href="Algebras.Algebras.html#1968" class="Module">algebra</a>

 <a id="2500" href="Algebras.Algebras.html#2500" class="Function">algebra→Algebra</a> <a id="2516" class="Symbol">:</a> <a id="2518" href="Algebras.Algebras.html#1968" class="Record">algebra</a> <a id="2526" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2528" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="2530" class="Symbol">→</a> <a id="2532" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="2540" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2542" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a>
 <a id="2545" href="Algebras.Algebras.html#2500" class="Function">algebra→Algebra</a> <a id="2561" href="Algebras.Algebras.html#2561" class="Bound">𝑨</a> <a id="2563" class="Symbol">=</a> <a id="2565" class="Symbol">(</a><a id="2566" href="Algebras.Algebras.html#2063" class="Field">univ</a> <a id="2571" href="Algebras.Algebras.html#2561" class="Bound">𝑨</a> <a id="2573" href="Overture.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="2575" href="Algebras.Algebras.html#2076" class="Field">op</a> <a id="2578" href="Algebras.Algebras.html#2561" class="Bound">𝑨</a><a id="2579" class="Symbol">)</a>

 <a id="2583" href="Algebras.Algebras.html#2583" class="Function">Algebra→algebra</a> <a id="2599" class="Symbol">:</a> <a id="2601" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="2609" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2611" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="2613" class="Symbol">→</a> <a id="2615" href="Algebras.Algebras.html#1968" class="Record">algebra</a> <a id="2623" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="2625" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a>
 <a id="2628" href="Algebras.Algebras.html#2583" class="Function">Algebra→algebra</a> <a id="2644" href="Algebras.Algebras.html#2644" class="Bound">𝑨</a> <a id="2646" class="Symbol">=</a> <a id="2648" href="Algebras.Algebras.html#2048" class="InductiveConstructor">mkalg</a> <a id="2654" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="2656" href="Algebras.Algebras.html#2644" class="Bound">𝑨</a> <a id="2658" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="2660" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="2662" href="Algebras.Algebras.html#2644" class="Bound">𝑨</a> <a id="2664" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a>

</pre>




#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol. This looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with, so we will use this new notation almost exclusively in the remaining modules of the [UALib][].

<pre class="Agda">

 <a id="3092" href="Algebras.Algebras.html#3092" class="Function Operator">_̂_</a> <a id="3096" class="Symbol">:</a> <a id="3098" class="Symbol">(</a><a id="3099" href="Algebras.Algebras.html#3099" class="Bound">𝑓</a> <a id="3101" class="Symbol">:</a> <a id="3103" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="3105" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="3107" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a><a id="3108" class="Symbol">)(</a><a id="3110" href="Algebras.Algebras.html#3110" class="Bound">𝑨</a> <a id="3112" class="Symbol">:</a> <a id="3114" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="3122" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3124" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a><a id="3125" class="Symbol">)</a> <a id="3127" class="Symbol">→</a> <a id="3129" class="Symbol">(</a><a id="3130" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="3132" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="3134" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="3136" href="Algebras.Algebras.html#3099" class="Bound">𝑓</a>  <a id="3139" class="Symbol">→</a>  <a id="3142" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="3144" href="Algebras.Algebras.html#3110" class="Bound">𝑨</a> <a id="3146" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a><a id="3147" class="Symbol">)</a> <a id="3149" class="Symbol">→</a> <a id="3151" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="3153" href="Algebras.Algebras.html#3110" class="Bound">𝑨</a> <a id="3155" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a>

 <a id="3159" href="Algebras.Algebras.html#3159" class="Bound">𝑓</a> <a id="3161" href="Algebras.Algebras.html#3092" class="Function Operator">̂</a> <a id="3163" href="Algebras.Algebras.html#3163" class="Bound">𝑨</a> <a id="3165" class="Symbol">=</a> <a id="3167" class="Symbol">λ</a> <a id="3169" href="Algebras.Algebras.html#3169" class="Bound">𝑎</a> <a id="3171" class="Symbol">→</a> <a id="3173" class="Symbol">(</a><a id="3174" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="3176" href="Algebras.Algebras.html#3163" class="Bound">𝑨</a> <a id="3178" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="3180" href="Algebras.Algebras.html#3159" class="Bound">𝑓</a><a id="3181" class="Symbol">)</a> <a id="3183" href="Algebras.Algebras.html#3169" class="Bound">𝑎</a>

</pre>

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if `𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎` denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.


#### <a id="arbitrarily-many-variable-symbols">Arbitrarily many variable symbols</a>

We sometimes want to assume that we have at our disposal an arbitrary collection `X` of variable symbols such that, for every algebra `𝑨`, no matter the type of its domain, we have a surjective map of type `X → ∣ 𝑨 ∣`, from variable symbols onto the domain of `𝑨`.  We may use the following definition to express this assumption when we need it.

<pre class="Agda">

 <a id="3862" href="Algebras.Algebras.html#3862" class="Function Operator">_↠_</a> <a id="3866" class="Symbol">:</a> <a id="3868" class="Symbol">{</a><a id="3869" href="Algebras.Algebras.html#3869" class="Bound">𝓧</a> <a id="3871" class="Symbol">:</a> <a id="3873" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3881" class="Symbol">}</a> <a id="3883" class="Symbol">→</a> <a id="3885" href="Algebras.Algebras.html#3869" class="Bound">𝓧</a> <a id="3887" href="Universes.html#403" class="Function Operator">̇</a> <a id="3889" class="Symbol">→</a> <a id="3891" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="3899" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3901" href="Algebras.Algebras.html#2458" class="Bound">𝑆</a> <a id="3903" class="Symbol">→</a> <a id="3905" href="Algebras.Algebras.html#3869" class="Bound">𝓧</a> <a id="3907" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3909" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="3911" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3914" href="Algebras.Algebras.html#3914" class="Bound">X</a> <a id="3916" href="Algebras.Algebras.html#3862" class="Function Operator">↠</a> <a id="3918" href="Algebras.Algebras.html#3918" class="Bound">𝑨</a> <a id="3920" class="Symbol">=</a> <a id="3922" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3924" href="Algebras.Algebras.html#3924" class="Bound">h</a> <a id="3926" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3928" class="Symbol">(</a><a id="3929" href="Algebras.Algebras.html#3914" class="Bound">X</a> <a id="3931" class="Symbol">→</a> <a id="3933" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="3935" href="Algebras.Algebras.html#3918" class="Bound">𝑨</a> <a id="3937" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a><a id="3938" class="Symbol">)</a> <a id="3940" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3942" href="Overture.Inverses.html#2015" class="Function">Epic</a> <a id="3947" href="Algebras.Algebras.html#3924" class="Bound">h</a>

</pre>

Now we can assert, in a specific module, the existence of the surjective map described above by including the following line in that module's declaration, like so.

<pre class="Agda">

<a id="4141" class="Keyword">module</a> <a id="4148" href="Algebras.Algebras.html#4148" class="Module">_</a> <a id="4150" class="Symbol">{</a><a id="4151" href="Algebras.Algebras.html#4151" class="Bound">𝓧</a> <a id="4153" class="Symbol">:</a> <a id="4155" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4163" class="Symbol">}{</a><a id="4165" href="Algebras.Algebras.html#4165" class="Bound">X</a> <a id="4167" class="Symbol">:</a> <a id="4169" href="Algebras.Algebras.html#4151" class="Bound">𝓧</a> <a id="4171" href="Universes.html#403" class="Function Operator">̇</a><a id="4172" class="Symbol">}{</a><a id="4174" href="Algebras.Algebras.html#4174" class="Bound">𝑆</a> <a id="4176" class="Symbol">:</a> <a id="4178" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="4188" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="4190" href="Universes.html#262" class="Generalizable">𝓥</a><a id="4191" class="Symbol">}</a>
         <a id="4202" class="Symbol">{</a><a id="4203" href="Algebras.Algebras.html#4203" class="Bound">𝕏</a> <a id="4205" class="Symbol">:</a> <a id="4207" class="Symbol">(</a><a id="4208" href="Algebras.Algebras.html#4208" class="Bound">𝑨</a> <a id="4210" class="Symbol">:</a> <a id="4212" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="4220" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4222" href="Algebras.Algebras.html#4174" class="Bound">𝑆</a><a id="4223" class="Symbol">)</a> <a id="4225" class="Symbol">→</a> <a id="4227" href="Algebras.Algebras.html#4165" class="Bound">X</a> <a id="4229" href="Algebras.Algebras.html#3862" class="Function Operator">↠</a> <a id="4231" href="Algebras.Algebras.html#4208" class="Bound">𝑨</a><a id="4232" class="Symbol">}</a> <a id="4234" class="Keyword">where</a>

</pre>

Then fst(𝕏 𝑨) will denote the surjective map h₀ : X → ∣ 𝑨 ∣, and snd(𝕏 𝑨) will be a proof that h₀ is surjective.




#### <a id="lifts-of-algebras">Level lifting algebra types</a>

Recall, in the [section on level lifting and lowering](Overture.Lifts.html#level-lifting-and-lowering), we described the difficulties one may encounter when working with a noncumulative universe hierarchy. We made a promise to provide some domain-specific level lifting and level lowering methods. Here we fulfill this promise by supplying a couple of bespoke tools designed specifically for our operation and algebra types.

<pre class="Agda">


<a id="4875" class="Keyword">module</a> <a id="4882" href="Algebras.Algebras.html#4882" class="Module">_</a> <a id="4884" class="Symbol">{</a><a id="4885" href="Algebras.Algebras.html#4885" class="Bound">I</a> <a id="4887" class="Symbol">:</a> <a id="4889" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4891" href="Universes.html#403" class="Function Operator">̇</a><a id="4892" class="Symbol">}{</a><a id="4894" href="Algebras.Algebras.html#4894" class="Bound">A</a> <a id="4896" class="Symbol">:</a> <a id="4898" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="4900" href="Universes.html#403" class="Function Operator">̇</a><a id="4901" class="Symbol">}</a> <a id="4903" class="Keyword">where</a>

 <a id="4911" class="Keyword">open</a> <a id="4916" href="Overture.Lifts.html#2996" class="Module">Lift</a>

 <a id="4923" href="Algebras.Algebras.html#4923" class="Function">Lift-op</a> <a id="4931" class="Symbol">:</a> <a id="4933" class="Symbol">((</a><a id="4935" href="Algebras.Algebras.html#4885" class="Bound">I</a> <a id="4937" class="Symbol">→</a> <a id="4939" href="Algebras.Algebras.html#4894" class="Bound">A</a><a id="4940" class="Symbol">)</a> <a id="4942" class="Symbol">→</a> <a id="4944" href="Algebras.Algebras.html#4894" class="Bound">A</a><a id="4945" class="Symbol">)</a> <a id="4947" class="Symbol">→</a> <a id="4949" class="Symbol">(</a><a id="4950" href="Algebras.Algebras.html#4950" class="Bound">𝓦</a> <a id="4952" class="Symbol">:</a> <a id="4954" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4962" class="Symbol">)</a> <a id="4964" class="Symbol">→</a> <a id="4966" class="Symbol">((</a><a id="4968" href="Algebras.Algebras.html#4885" class="Bound">I</a> <a id="4970" class="Symbol">→</a> <a id="4972" href="Overture.Lifts.html#2996" class="Record">Lift</a><a id="4976" class="Symbol">{</a><a id="4977" href="Algebras.Algebras.html#4950" class="Bound">𝓦</a><a id="4978" class="Symbol">}</a> <a id="4980" href="Algebras.Algebras.html#4894" class="Bound">A</a><a id="4981" class="Symbol">)</a> <a id="4983" class="Symbol">→</a> <a id="4985" href="Overture.Lifts.html#2996" class="Record">Lift</a> <a id="4990" class="Symbol">{</a><a id="4991" href="Algebras.Algebras.html#4950" class="Bound">𝓦</a><a id="4992" class="Symbol">}</a> <a id="4994" href="Algebras.Algebras.html#4894" class="Bound">A</a><a id="4995" class="Symbol">)</a>
 <a id="4998" href="Algebras.Algebras.html#4923" class="Function">Lift-op</a> <a id="5006" href="Algebras.Algebras.html#5006" class="Bound">f</a> <a id="5008" href="Algebras.Algebras.html#5008" class="Bound">𝓦</a> <a id="5010" class="Symbol">=</a> <a id="5012" class="Symbol">λ</a> <a id="5014" href="Algebras.Algebras.html#5014" class="Bound">x</a> <a id="5016" class="Symbol">→</a> <a id="5018" href="Overture.Lifts.html#3058" class="InductiveConstructor">lift</a> <a id="5023" class="Symbol">(</a><a id="5024" href="Algebras.Algebras.html#5006" class="Bound">f</a> <a id="5026" class="Symbol">(λ</a> <a id="5029" href="Algebras.Algebras.html#5029" class="Bound">i</a> <a id="5031" class="Symbol">→</a> <a id="5033" href="Overture.Lifts.html#3070" class="Field">lower</a> <a id="5039" class="Symbol">(</a><a id="5040" href="Algebras.Algebras.html#5014" class="Bound">x</a> <a id="5042" href="Algebras.Algebras.html#5029" class="Bound">i</a><a id="5043" class="Symbol">)))</a>

<a id="5048" class="Keyword">module</a> <a id="5055" href="Algebras.Algebras.html#5055" class="Module">_</a> <a id="5057" class="Symbol">{</a><a id="5058" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a> <a id="5060" class="Symbol">:</a> <a id="5062" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="5072" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="5074" href="Universes.html#262" class="Generalizable">𝓥</a><a id="5075" class="Symbol">}</a>  <a id="5078" class="Keyword">where</a>

 <a id="5086" class="Keyword">open</a> <a id="5091" href="Algebras.Algebras.html#1968" class="Module">algebra</a>

 <a id="5101" href="Algebras.Algebras.html#5101" class="Function">Lift-alg</a> <a id="5110" class="Symbol">:</a> <a id="5112" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="5120" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5122" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a> <a id="5124" class="Symbol">→</a> <a id="5126" class="Symbol">(</a><a id="5127" href="Algebras.Algebras.html#5127" class="Bound">𝓦</a> <a id="5129" class="Symbol">:</a> <a id="5131" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5139" class="Symbol">)</a> <a id="5141" class="Symbol">→</a> <a id="5143" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="5151" class="Symbol">(</a><a id="5152" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5154" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5156" href="Algebras.Algebras.html#5127" class="Bound">𝓦</a><a id="5157" class="Symbol">)</a> <a id="5159" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a>
 <a id="5162" href="Algebras.Algebras.html#5101" class="Function">Lift-alg</a> <a id="5171" href="Algebras.Algebras.html#5171" class="Bound">𝑨</a> <a id="5173" href="Algebras.Algebras.html#5173" class="Bound">𝓦</a> <a id="5175" class="Symbol">=</a> <a id="5177" href="Overture.Lifts.html#2996" class="Record">Lift</a> <a id="5182" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="5184" href="Algebras.Algebras.html#5171" class="Bound">𝑨</a> <a id="5186" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="5188" href="Overture.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="5190" class="Symbol">(λ</a> <a id="5193" class="Symbol">(</a><a id="5194" href="Algebras.Algebras.html#5194" class="Bound">𝑓</a> <a id="5196" class="Symbol">:</a> <a id="5198" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="5200" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a> <a id="5202" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a><a id="5203" class="Symbol">)</a> <a id="5205" class="Symbol">→</a> <a id="5207" href="Algebras.Algebras.html#4923" class="Function">Lift-op</a> <a id="5215" class="Symbol">(</a><a id="5216" href="Algebras.Algebras.html#5194" class="Bound">𝑓</a> <a id="5218" href="Algebras.Algebras.html#3092" class="Function Operator">̂</a> <a id="5220" href="Algebras.Algebras.html#5171" class="Bound">𝑨</a><a id="5221" class="Symbol">)</a> <a id="5223" href="Algebras.Algebras.html#5173" class="Bound">𝓦</a><a id="5224" class="Symbol">)</a>

 <a id="5228" href="Algebras.Algebras.html#5228" class="Function">Lift-alg-record-type</a> <a id="5249" class="Symbol">:</a> <a id="5251" href="Algebras.Algebras.html#1968" class="Record">algebra</a> <a id="5259" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5261" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a> <a id="5263" class="Symbol">→</a> <a id="5265" class="Symbol">(</a><a id="5266" href="Algebras.Algebras.html#5266" class="Bound">𝓦</a> <a id="5268" class="Symbol">:</a> <a id="5270" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5278" class="Symbol">)</a> <a id="5280" class="Symbol">→</a> <a id="5282" href="Algebras.Algebras.html#1968" class="Record">algebra</a> <a id="5290" class="Symbol">(</a><a id="5291" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="5293" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5295" href="Algebras.Algebras.html#5266" class="Bound">𝓦</a><a id="5296" class="Symbol">)</a> <a id="5298" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a>
 <a id="5301" href="Algebras.Algebras.html#5228" class="Function">Lift-alg-record-type</a> <a id="5322" href="Algebras.Algebras.html#5322" class="Bound">𝑨</a> <a id="5324" href="Algebras.Algebras.html#5324" class="Bound">𝓦</a> <a id="5326" class="Symbol">=</a> <a id="5328" href="Algebras.Algebras.html#2048" class="InductiveConstructor">mkalg</a> <a id="5334" class="Symbol">(</a><a id="5335" href="Overture.Lifts.html#2996" class="Record">Lift</a> <a id="5340" class="Symbol">(</a><a id="5341" href="Algebras.Algebras.html#2063" class="Field">univ</a> <a id="5346" href="Algebras.Algebras.html#5322" class="Bound">𝑨</a><a id="5347" class="Symbol">))</a> <a id="5350" class="Symbol">(λ</a> <a id="5353" class="Symbol">(</a><a id="5354" href="Algebras.Algebras.html#5354" class="Bound">f</a> <a id="5356" class="Symbol">:</a> <a id="5358" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="5360" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a> <a id="5362" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a><a id="5363" class="Symbol">)</a> <a id="5365" class="Symbol">→</a> <a id="5367" href="Algebras.Algebras.html#4923" class="Function">Lift-op</a> <a id="5375" class="Symbol">((</a><a id="5377" href="Algebras.Algebras.html#2076" class="Field">op</a> <a id="5380" href="Algebras.Algebras.html#5322" class="Bound">𝑨</a><a id="5381" class="Symbol">)</a> <a id="5383" href="Algebras.Algebras.html#5354" class="Bound">f</a><a id="5384" class="Symbol">)</a> <a id="5386" href="Algebras.Algebras.html#5324" class="Bound">𝓦</a><a id="5387" class="Symbol">)</a>

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

 <a id="6885" href="Algebras.Algebras.html#6885" class="Function">compatible</a> <a id="6896" class="Symbol">:</a> <a id="6898" class="Symbol">(</a><a id="6899" href="Algebras.Algebras.html#6899" class="Bound">𝑨</a> <a id="6901" class="Symbol">:</a> <a id="6903" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="6911" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6913" href="Algebras.Algebras.html#5058" class="Bound">𝑆</a><a id="6914" class="Symbol">)</a> <a id="6916" class="Symbol">→</a> <a id="6918" href="Relations.Discrete.html#6780" class="Function">Rel</a> <a id="6922" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="6924" href="Algebras.Algebras.html#6899" class="Bound">𝑨</a> <a id="6926" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="6928" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6930" class="Symbol">→</a> <a id="6932" href="Algebras.Algebras.html#5072" class="Bound">𝓞</a> <a id="6934" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6936" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="6938" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6940" href="Algebras.Algebras.html#5074" class="Bound">𝓥</a> <a id="6942" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6944" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="6946" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="6949" href="Algebras.Algebras.html#6885" class="Function">compatible</a>  <a id="6961" href="Algebras.Algebras.html#6961" class="Bound">𝑨</a> <a id="6963" href="Algebras.Algebras.html#6963" class="Bound">R</a> <a id="6965" class="Symbol">=</a> <a id="6967" class="Symbol">∀</a> <a id="6969" href="Algebras.Algebras.html#6969" class="Bound">𝑓</a> <a id="6971" class="Symbol">→</a> <a id="6973" class="Symbol">(</a><a id="6974" href="Algebras.Algebras.html#6969" class="Bound">𝑓</a> <a id="6976" href="Algebras.Algebras.html#3092" class="Function Operator">̂</a> <a id="6978" href="Algebras.Algebras.html#6961" class="Bound">𝑨</a><a id="6979" class="Symbol">)</a> <a id="6981" href="Relations.Discrete.html#9896" class="Function Operator">|:</a> <a id="6984" href="Algebras.Algebras.html#6963" class="Bound">R</a>

</pre>

Recall, the `compatible-fun` type was defined in [Relations.Discrete][] module.



---------------------------------------



#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations*</a>

This section presents the `continuous-compatibility` submodule of the [Algebras.Algebras][] module.<sup>[*](Algebras.Algebras.html#fn0)</sup>


Next we define a type that represents *compatibility of a continuous relation* with all operations of an algebra. We start by defining compatibility of a continuous relations with a single operation.

<pre class="Agda">

<a id="7579" class="Keyword">module</a> <a id="continuous-compatibility"></a><a id="7586" href="Algebras.Algebras.html#7586" class="Module">continuous-compatibility</a> <a id="7611" class="Symbol">{</a><a id="7612" href="Algebras.Algebras.html#7612" class="Bound">𝑆</a> <a id="7614" class="Symbol">:</a> <a id="7616" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="7626" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="7628" href="Universes.html#262" class="Generalizable">𝓥</a><a id="7629" class="Symbol">}</a> <a id="7631" class="Symbol">{</a><a id="7632" href="Algebras.Algebras.html#7632" class="Bound">𝑨</a> <a id="7634" class="Symbol">:</a> <a id="7636" href="Algebras.Algebras.html#777" class="Function">Algebra</a> <a id="7644" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="7646" href="Algebras.Algebras.html#7612" class="Bound">𝑆</a><a id="7647" class="Symbol">}</a> <a id="7649" class="Symbol">{</a><a id="7650" href="Algebras.Algebras.html#7650" class="Bound">I</a> <a id="7652" class="Symbol">:</a> <a id="7654" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="7656" href="Universes.html#403" class="Function Operator">̇</a><a id="7657" class="Symbol">}</a> <a id="7659" class="Keyword">where</a>

 <a id="7667" class="Keyword">open</a> <a id="7672" class="Keyword">import</a> <a id="7679" href="Relations.Continuous.html" class="Module">Relations.Continuous</a> <a id="7700" class="Keyword">using</a> <a id="7706" class="Symbol">(</a><a id="7707" href="Relations.Continuous.html#3237" class="Function">ContRel</a><a id="7714" class="Symbol">;</a> <a id="7716" href="Relations.Continuous.html#3860" class="Function">eval-cont-rel</a><a id="7729" class="Symbol">;</a> <a id="7731" href="Relations.Continuous.html#3961" class="Function">cont-compatible-fun</a><a id="7750" class="Symbol">)</a>


 <a id="continuous-compatibility.cont-compatible-op"></a><a id="7755" href="Algebras.Algebras.html#7755" class="Function">cont-compatible-op</a> <a id="7774" class="Symbol">:</a> <a id="7776" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="7778" href="Algebras.Algebras.html#7612" class="Bound">𝑆</a> <a id="7780" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="7782" class="Symbol">→</a> <a id="7784" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="7792" href="Algebras.Algebras.html#7650" class="Bound">I</a> <a id="7794" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="7796" href="Algebras.Algebras.html#7632" class="Bound">𝑨</a> <a id="7798" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="7800" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7802" class="Symbol">→</a> <a id="7804" href="Algebras.Algebras.html#7644" class="Bound">𝓤</a> <a id="7806" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7808" href="Algebras.Algebras.html#7628" class="Bound">𝓥</a> <a id="7810" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="7812" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="7814" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="7817" href="Algebras.Algebras.html#7755" class="Function">cont-compatible-op</a> <a id="7836" href="Algebras.Algebras.html#7836" class="Bound">𝑓</a> <a id="7838" href="Algebras.Algebras.html#7838" class="Bound">R</a> <a id="7840" class="Symbol">=</a> <a id="7842" href="Relations.Continuous.html#3961" class="Function">cont-compatible-fun</a> <a id="7862" class="Symbol">(</a><a id="7863" href="Algebras.Algebras.html#7836" class="Bound">𝑓</a> <a id="7865" href="Algebras.Algebras.html#3092" class="Function Operator">̂</a> <a id="7867" href="Algebras.Algebras.html#7632" class="Bound">𝑨</a><a id="7868" class="Symbol">)</a> <a id="7870" href="Algebras.Algebras.html#7838" class="Bound">R</a>

</pre>

In case it helps the reader understand `con-compatible-op`, we redefine it explicitly without the help of `con-compatible-fun`.

<pre class="Agda">

 <a id="continuous-compatibility.cont-compatible-op&#39;"></a><a id="8029" href="Algebras.Algebras.html#8029" class="Function">cont-compatible-op&#39;</a> <a id="8049" class="Symbol">:</a> <a id="8051" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8053" href="Algebras.Algebras.html#7612" class="Bound">𝑆</a> <a id="8055" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8057" class="Symbol">→</a> <a id="8059" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="8067" href="Algebras.Algebras.html#7650" class="Bound">I</a> <a id="8069" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8071" href="Algebras.Algebras.html#7632" class="Bound">𝑨</a> <a id="8073" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8075" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8077" class="Symbol">→</a> <a id="8079" href="Algebras.Algebras.html#7644" class="Bound">𝓤</a> <a id="8081" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8083" href="Algebras.Algebras.html#7628" class="Bound">𝓥</a> <a id="8085" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8087" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8089" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8092" href="Algebras.Algebras.html#8029" class="Function">cont-compatible-op&#39;</a> <a id="8112" href="Algebras.Algebras.html#8112" class="Bound">𝑓</a> <a id="8114" href="Algebras.Algebras.html#8114" class="Bound">R</a> <a id="8116" class="Symbol">=</a> <a id="8118" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8120" href="Algebras.Algebras.html#8120" class="Bound">𝒂</a> <a id="8122" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8124" class="Symbol">(</a><a id="8125" href="Algebras.Algebras.html#7650" class="Bound">I</a> <a id="8127" class="Symbol">→</a> <a id="8129" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="8131" href="Algebras.Algebras.html#7612" class="Bound">𝑆</a> <a id="8133" href="Overture.Preliminaries.html#13749" class="Function Operator">∥</a> <a id="8135" href="Algebras.Algebras.html#8112" class="Bound">𝑓</a> <a id="8137" class="Symbol">→</a> <a id="8139" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8141" href="Algebras.Algebras.html#7632" class="Bound">𝑨</a> <a id="8143" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a><a id="8144" class="Symbol">)</a> <a id="8146" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8148" class="Symbol">(</a><a id="8149" href="Relations.Continuous.html#3860" class="Function">eval-cont-rel</a> <a id="8163" href="Algebras.Algebras.html#8114" class="Bound">R</a> <a id="8165" href="Algebras.Algebras.html#8120" class="Bound">𝒂</a> <a id="8167" class="Symbol">→</a> <a id="8169" href="Algebras.Algebras.html#8114" class="Bound">R</a> <a id="8171" class="Symbol">λ</a> <a id="8173" href="Algebras.Algebras.html#8173" class="Bound">i</a> <a id="8175" class="Symbol">→</a> <a id="8177" class="Symbol">(</a><a id="8178" href="Algebras.Algebras.html#8112" class="Bound">𝑓</a> <a id="8180" href="Algebras.Algebras.html#3092" class="Function Operator">̂</a> <a id="8182" href="Algebras.Algebras.html#7632" class="Bound">𝑨</a><a id="8183" class="Symbol">)(</a><a id="8185" href="Algebras.Algebras.html#8120" class="Bound">𝒂</a> <a id="8187" href="Algebras.Algebras.html#8173" class="Bound">i</a><a id="8188" class="Symbol">))</a>

</pre>

With `cont-compatible-op` in hand, it is a trivial matter to define a type that represents *compatibility of a continuous relation with an algebra*.

<pre class="Agda">

 <a id="continuous-compatibility.cont-compatible"></a><a id="8369" href="Algebras.Algebras.html#8369" class="Function">cont-compatible</a> <a id="8385" class="Symbol">:</a> <a id="8387" href="Relations.Continuous.html#3237" class="Function">ContRel</a> <a id="8395" href="Algebras.Algebras.html#7650" class="Bound">I</a> <a id="8397" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8399" href="Algebras.Algebras.html#7632" class="Bound">𝑨</a> <a id="8401" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8403" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8405" class="Symbol">→</a> <a id="8407" href="Algebras.Algebras.html#7626" class="Bound">𝓞</a> <a id="8409" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8411" href="Algebras.Algebras.html#7644" class="Bound">𝓤</a> <a id="8413" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8415" href="Algebras.Algebras.html#7628" class="Bound">𝓥</a> <a id="8417" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="8419" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="8421" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="8424" href="Algebras.Algebras.html#8369" class="Function">cont-compatible</a> <a id="8440" href="Algebras.Algebras.html#8440" class="Bound">R</a> <a id="8442" class="Symbol">=</a> <a id="8444" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="8446" href="Algebras.Algebras.html#8446" class="Bound">𝑓</a> <a id="8448" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="8450" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8452" href="Algebras.Algebras.html#7612" class="Bound">𝑆</a> <a id="8454" href="Overture.Preliminaries.html#13697" class="Function Operator">∣</a> <a id="8456" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="8458" href="Algebras.Algebras.html#7755" class="Function">cont-compatible-op</a> <a id="8477" href="Algebras.Algebras.html#8446" class="Bound">𝑓</a> <a id="8479" href="Algebras.Algebras.html#8440" class="Bound">R</a>

</pre>



--------------------------------------

<sup>[*]</sup><span class="footnote" id="fn0"> Sections marked with an asterisk include new types that are more abstract and general (and frankly more interesting) than the ones presented in other sections.  Consequently, such sections expect a higher degree of sophistication and/or effort from the reader/user. Moreover, the types defined in starred sections are used in only a few other places in the [Agda UALib][], so they may be safely skimmed over or skipped.</span>

<br>
<br>

[← Algebras.Signatures](Algebras.Signatures.html)
<span style="float:right;">[Algebras.Products →](Algebras.Products.html)</span>


{% include UALib.Links.md %}
