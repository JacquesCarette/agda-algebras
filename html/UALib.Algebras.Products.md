---
layout: default
title : UALib.Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="product-algebra-types">Product Algebra Types</a>

This section presents the [UALib.Algebras.Products][] module of the [Agda Universal Algebra Library][].

We define products of algebras for both the Sigma type representation (the one we use most often) and the record type representation.

<pre class="Agda">

<a id="453" class="Symbol">{-#</a> <a id="457" class="Keyword">OPTIONS</a> <a id="465" class="Pragma">--without-K</a> <a id="477" class="Pragma">--exact-split</a> <a id="491" class="Pragma">--safe</a> <a id="498" class="Symbol">#-}</a>

<a id="503" class="Keyword">module</a> <a id="510" href="UALib.Algebras.Products.html" class="Module">UALib.Algebras.Products</a> <a id="534" class="Keyword">where</a>


<a id="542" class="Keyword">open</a> <a id="547" class="Keyword">import</a> <a id="554" href="UALib.Algebras.Algebras.html" class="Module">UALib.Algebras.Algebras</a> <a id="578" class="Keyword">public</a>


<a id="587" class="Keyword">module</a> <a id="594" href="UALib.Algebras.Products.html#594" class="Module">_</a> <a id="596" class="Symbol">{</a><a id="597" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a> <a id="599" class="Symbol">:</a> <a id="601" href="universes.html#551" class="Postulate">Universe</a><a id="609" class="Symbol">}{</a><a id="611" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a> <a id="613" class="Symbol">:</a> <a id="615" href="UALib.Algebras.Signatures.html#1324" class="Function">Signature</a> <a id="625" href="universes.html#613" class="Generalizable">𝓞</a> <a id="627" href="universes.html#617" class="Generalizable">𝓥</a><a id="628" class="Symbol">}</a>  <a id="631" class="Keyword">where</a>

 <a id="639" class="Comment">-- product for algebras of sigma type</a>
 <a id="678" href="UALib.Algebras.Products.html#678" class="Function">⨅</a> <a id="680" class="Symbol">:</a> <a id="682" class="Symbol">{</a><a id="683" href="UALib.Algebras.Products.html#683" class="Bound">𝓘</a> <a id="685" class="Symbol">:</a> <a id="687" href="universes.html#551" class="Postulate">Universe</a><a id="695" class="Symbol">}{</a><a id="697" href="UALib.Algebras.Products.html#697" class="Bound">I</a> <a id="699" class="Symbol">:</a> <a id="701" href="UALib.Algebras.Products.html#683" class="Bound">𝓘</a> <a id="703" href="universes.html#758" class="Function Operator">̇</a> <a id="705" class="Symbol">}(</a><a id="707" href="UALib.Algebras.Products.html#707" class="Bound">𝒜</a> <a id="709" class="Symbol">:</a> <a id="711" href="UALib.Algebras.Products.html#697" class="Bound">I</a> <a id="713" class="Symbol">→</a> <a id="715" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="723" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a> <a id="725" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a> <a id="727" class="Symbol">)</a> <a id="729" class="Symbol">→</a> <a id="731" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="739" class="Symbol">(</a><a id="740" href="UALib.Algebras.Products.html#683" class="Bound">𝓘</a> <a id="742" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="744" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a><a id="745" class="Symbol">)</a> <a id="747" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a>
 <a id="750" href="UALib.Algebras.Products.html#678" class="Function">⨅</a> <a id="752" class="Symbol">{</a><a id="753" href="UALib.Algebras.Products.html#753" class="Bound">𝓘</a><a id="754" class="Symbol">}{</a><a id="756" href="UALib.Algebras.Products.html#756" class="Bound">I</a><a id="757" class="Symbol">}</a> <a id="759" href="UALib.Algebras.Products.html#759" class="Bound">𝒜</a> <a id="761" class="Symbol">=</a>
  <a id="765" class="Symbol">((</a><a id="767" href="UALib.Algebras.Products.html#767" class="Bound">i</a> <a id="769" class="Symbol">:</a> <a id="771" href="UALib.Algebras.Products.html#756" class="Bound">I</a><a id="772" class="Symbol">)</a> <a id="774" class="Symbol">→</a> <a id="776" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a> <a id="778" href="UALib.Algebras.Products.html#759" class="Bound">𝒜</a> <a id="780" href="UALib.Algebras.Products.html#767" class="Bound">i</a> <a id="782" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a><a id="783" class="Symbol">)</a> <a id="785" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a> <a id="787" class="Symbol">λ(</a><a id="789" href="UALib.Algebras.Products.html#789" class="Bound">f</a> <a id="791" class="Symbol">:</a> <a id="793" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a> <a id="795" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a> <a id="797" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a><a id="798" class="Symbol">)(</a><a id="800" href="UALib.Algebras.Products.html#800" class="Bound">𝒂</a> <a id="802" class="Symbol">:</a> <a id="804" href="UALib.Prelude.Preliminaries.html#10366" class="Function Operator">∥</a> <a id="806" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a> <a id="808" href="UALib.Prelude.Preliminaries.html#10366" class="Function Operator">∥</a> <a id="810" href="UALib.Algebras.Products.html#789" class="Bound">f</a> <a id="812" class="Symbol">→</a> <a id="814" class="Symbol">(</a><a id="815" href="UALib.Algebras.Products.html#815" class="Bound">j</a> <a id="817" class="Symbol">:</a> <a id="819" href="UALib.Algebras.Products.html#756" class="Bound">I</a><a id="820" class="Symbol">)</a> <a id="822" class="Symbol">→</a> <a id="824" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a> <a id="826" href="UALib.Algebras.Products.html#759" class="Bound">𝒜</a> <a id="828" href="UALib.Algebras.Products.html#815" class="Bound">j</a> <a id="830" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a><a id="831" class="Symbol">)(</a><a id="833" href="UALib.Algebras.Products.html#833" class="Bound">i</a> <a id="835" class="Symbol">:</a> <a id="837" href="UALib.Algebras.Products.html#756" class="Bound">I</a><a id="838" class="Symbol">)</a> <a id="840" class="Symbol">→</a> <a id="842" class="Symbol">(</a><a id="843" href="UALib.Algebras.Products.html#789" class="Bound">f</a> <a id="845" href="UALib.Algebras.Algebras.html#3426" class="Function Operator">̂</a> <a id="847" href="UALib.Algebras.Products.html#759" class="Bound">𝒜</a> <a id="849" href="UALib.Algebras.Products.html#833" class="Bound">i</a><a id="850" class="Symbol">)</a> <a id="852" class="Symbol">λ{</a><a id="854" href="UALib.Algebras.Products.html#854" class="Bound">x</a> <a id="856" class="Symbol">→</a> <a id="858" href="UALib.Algebras.Products.html#800" class="Bound">𝒂</a> <a id="860" href="UALib.Algebras.Products.html#854" class="Bound">x</a> <a id="862" href="UALib.Algebras.Products.html#833" class="Bound">i</a><a id="863" class="Symbol">}</a>

 <a id="867" href="UALib.Algebras.Products.html#867" class="Function">⊓</a> <a id="869" class="Symbol">:</a> <a id="871" class="Symbol">{</a><a id="872" href="UALib.Algebras.Products.html#872" class="Bound">I</a> <a id="874" class="Symbol">:</a> <a id="876" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a> <a id="878" href="universes.html#758" class="Function Operator">̇</a> <a id="880" class="Symbol">}(</a><a id="882" href="UALib.Algebras.Products.html#882" class="Bound">𝒜</a> <a id="884" class="Symbol">:</a> <a id="886" href="UALib.Algebras.Products.html#872" class="Bound">I</a> <a id="888" class="Symbol">→</a> <a id="890" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="898" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a> <a id="900" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a> <a id="902" class="Symbol">)</a> <a id="904" class="Symbol">→</a> <a id="906" href="UALib.Algebras.Algebras.html#811" class="Function">Algebra</a> <a id="914" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a> <a id="916" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a>
 <a id="919" href="UALib.Algebras.Products.html#867" class="Function">⊓</a> <a id="921" class="Symbol">=</a> <a id="923" href="UALib.Algebras.Products.html#678" class="Function">⨅</a> <a id="925" class="Symbol">{</a><a id="926" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a><a id="927" class="Symbol">}</a>

 <a id="931" class="Keyword">open</a> <a id="936" href="UALib.Algebras.Algebras.html#2393" class="Module">algebra</a>

 <a id="946" class="Comment">-- product for algebras of record type</a>
 <a id="986" href="UALib.Algebras.Products.html#986" class="Function">⨅&#39;</a> <a id="989" class="Symbol">:</a> <a id="991" class="Symbol">{</a><a id="992" href="UALib.Algebras.Products.html#992" class="Bound">𝓘</a> <a id="994" class="Symbol">:</a> <a id="996" href="universes.html#551" class="Postulate">Universe</a><a id="1004" class="Symbol">}{</a><a id="1006" href="UALib.Algebras.Products.html#1006" class="Bound">I</a> <a id="1008" class="Symbol">:</a> <a id="1010" href="UALib.Algebras.Products.html#992" class="Bound">𝓘</a> <a id="1012" href="universes.html#758" class="Function Operator">̇</a> <a id="1014" class="Symbol">}(</a><a id="1016" href="UALib.Algebras.Products.html#1016" class="Bound">𝒜</a> <a id="1018" class="Symbol">:</a> <a id="1020" href="UALib.Algebras.Products.html#1006" class="Bound">I</a> <a id="1022" class="Symbol">→</a> <a id="1024" href="UALib.Algebras.Algebras.html#2393" class="Record">algebra</a> <a id="1032" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a> <a id="1034" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a><a id="1035" class="Symbol">)</a> <a id="1037" class="Symbol">→</a> <a id="1039" href="UALib.Algebras.Algebras.html#2393" class="Record">algebra</a> <a id="1047" class="Symbol">(</a><a id="1048" href="UALib.Algebras.Products.html#992" class="Bound">𝓘</a> <a id="1050" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1052" href="UALib.Algebras.Products.html#597" class="Bound">𝓤</a><a id="1053" class="Symbol">)</a> <a id="1055" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a>
 <a id="1058" href="UALib.Algebras.Products.html#986" class="Function">⨅&#39;</a> <a id="1061" class="Symbol">{</a><a id="1062" href="UALib.Algebras.Products.html#1062" class="Bound">𝓘</a><a id="1063" class="Symbol">}{</a><a id="1065" href="UALib.Algebras.Products.html#1065" class="Bound">I</a><a id="1066" class="Symbol">}</a> <a id="1068" href="UALib.Algebras.Products.html#1068" class="Bound">𝒜</a> <a id="1070" class="Symbol">=</a> <a id="1072" class="Keyword">record</a>
                  <a id="1097" class="Symbol">{</a> <a id="1099" href="UALib.Algebras.Algebras.html#2491" class="Field">univ</a> <a id="1104" class="Symbol">=</a> <a id="1106" class="Symbol">(</a><a id="1107" href="UALib.Algebras.Products.html#1107" class="Bound">i</a> <a id="1109" class="Symbol">:</a> <a id="1111" href="UALib.Algebras.Products.html#1065" class="Bound">I</a><a id="1112" class="Symbol">)</a> <a id="1114" class="Symbol">→</a> <a id="1116" href="UALib.Algebras.Algebras.html#2491" class="Field">univ</a> <a id="1121" class="Symbol">(</a><a id="1122" href="UALib.Algebras.Products.html#1068" class="Bound">𝒜</a> <a id="1124" href="UALib.Algebras.Products.html#1107" class="Bound">i</a><a id="1125" class="Symbol">)</a>
                  <a id="1145" class="Symbol">;</a> <a id="1147" href="UALib.Algebras.Algebras.html#2505" class="Field">op</a> <a id="1150" class="Symbol">=</a> <a id="1152" class="Symbol">λ(</a><a id="1154" href="UALib.Algebras.Products.html#1154" class="Bound">f</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a> <a id="1160" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a> <a id="1162" href="UALib.Prelude.Preliminaries.html#10288" class="Function Operator">∣</a><a id="1163" class="Symbol">)</a>
                          <a id="1191" class="Symbol">(</a><a id="1192" href="UALib.Algebras.Products.html#1192" class="Bound">𝒂</a> <a id="1194" class="Symbol">:</a> <a id="1196" href="UALib.Prelude.Preliminaries.html#10366" class="Function Operator">∥</a> <a id="1198" href="UALib.Algebras.Products.html#611" class="Bound">𝑆</a> <a id="1200" href="UALib.Prelude.Preliminaries.html#10366" class="Function Operator">∥</a> <a id="1202" href="UALib.Algebras.Products.html#1154" class="Bound">f</a> <a id="1204" class="Symbol">→</a> <a id="1206" class="Symbol">(</a><a id="1207" href="UALib.Algebras.Products.html#1207" class="Bound">j</a> <a id="1209" class="Symbol">:</a> <a id="1211" href="UALib.Algebras.Products.html#1065" class="Bound">I</a><a id="1212" class="Symbol">)</a> <a id="1214" class="Symbol">→</a> <a id="1216" href="UALib.Algebras.Algebras.html#2491" class="Field">univ</a><a id="1220" class="Symbol">(</a><a id="1221" href="UALib.Algebras.Products.html#1068" class="Bound">𝒜</a> <a id="1223" href="UALib.Algebras.Products.html#1207" class="Bound">j</a><a id="1224" class="Symbol">))</a>
                          <a id="1253" class="Symbol">(</a><a id="1254" href="UALib.Algebras.Products.html#1254" class="Bound">i</a> <a id="1256" class="Symbol">:</a> <a id="1258" href="UALib.Algebras.Products.html#1065" class="Bound">I</a><a id="1259" class="Symbol">)</a> <a id="1261" class="Symbol">→</a> <a id="1263" class="Symbol">((</a><a id="1265" href="UALib.Algebras.Algebras.html#2505" class="Field">op</a> <a id="1268" class="Symbol">(</a><a id="1269" href="UALib.Algebras.Products.html#1068" class="Bound">𝒜</a> <a id="1271" href="UALib.Algebras.Products.html#1254" class="Bound">i</a><a id="1272" class="Symbol">))</a> <a id="1275" href="UALib.Algebras.Products.html#1154" class="Bound">f</a><a id="1276" class="Symbol">)</a>
                          <a id="1304" class="Symbol">λ{</a><a id="1306" href="UALib.Algebras.Products.html#1306" class="Bound">x</a> <a id="1308" class="Symbol">→</a> <a id="1310" href="UALib.Algebras.Products.html#1192" class="Bound">𝒂</a> <a id="1312" href="UALib.Algebras.Products.html#1306" class="Bound">x</a> <a id="1314" href="UALib.Algebras.Products.html#1254" class="Bound">i</a><a id="1315" class="Symbol">}</a>
                  <a id="1335" class="Symbol">}</a>


</pre>

-----------------------

[← UALib.Algebras.Algebras](UALib.Algebras.Algebras.html)
<span style="float:right;">[UALib.Algebras.Lifts →](UALib.Algebras.Lifts.html)</span>

{% include UALib.Links.md %}