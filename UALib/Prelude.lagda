---
layout: default
title : Prelude module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: Prelude.lagda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATED: 14 Jan 2021
REF: Parts of this module are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
     Below, MHE = Martin Hötzel Escardo.
-->

## <a id="prelude">Prelude</a>

This chapter presents the [Prelude][] module of the [Agda Universal Algebra Library][].

The source code for this module comprises the (literate) [Agda][] program that was used to generate the html page displaying the sentence you are now reading. This source code inhabits the file [Prelude.lagda][], which resides in the [git repository of the Agda UALib][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude where

open import Prelude.Preliminaries public
open import Prelude.Equality public
open import Prelude.Inverses public
open import Prelude.Extensionality public
open import Prelude.Lifts public

\end{code}

--------------------------------------

<p></p>

[← Preface](Preface.html)
<span style="float:right;">[Prelude.Preliminaries →](Prelude.Preliminaries.html)</span>

{% include UALib.Links.md %}
