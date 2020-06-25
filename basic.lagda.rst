.. file: basic.lagda.rst
.. Author: William DeMeo  <williamdemeo@gmail.com>
.. Date: 24 Dec 2019
.. Updated: 25 Jun 2020
.. Note: This was used for the second part of my talk at JMM Special Session.
.. Copyright (c) 2019 William DeMeo

.. _types for algebras:

Types for Algebras
===================

This chapter describes our formalization (in `Agda`_ ) of basic notions of universal algebra, such as operation, signature, and algebraic structure.  This formalization is implemented in an Agda module of the `agda-ualib`_ called ``basic``.

-----------------------------------

.. _preliminaries:

Preliminaries
-------------------------

After ``prelude`` (described in `agda preliminaries`_) the next module in `agda-ualib`_ is called ``basic``, which we now describe.

As usual, we start with some options, imports, and a module declaration.

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   open import prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣;
     _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; _×_; Π; _≡_)

   module basic where

-----------------------------------


.. _operations and signatures in agda:

Operations and signatures in Agda
---------------------------------

Operation
~~~~~~~~~~~

We define the type of **operations**, and give an example (the projections).

::

   -- Operations and projections
   Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
   Op I A = (I → A) → A

   π : {I : 𝓥 ̇} {A : 𝓤 ̇} → I → Op I A
   π i x = x i


The type ``Op`` encodes the arity of an operation as an arbitrary type ``I : 𝓥 ̇``, which gives us a very general way to represent an operation as a function type with domain ``I → A`` (the type of "tuples") and codomain ``A``.

The last two lines of the code block above codify the ``i``-th ``I``-ary projection operation on ``A``.

Signature
~~~~~~~~~~

We define an (algebraic) signature like this.

::

   -- 𝓞 is the universe in which the operation symbols lives
   -- 𝓥 is the universe in which the arities live
   Signature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
   Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , ( F → 𝓥 ̇ )

In the ``prelude`` module we defined the syntax ``∣_∣`` and ``∥_∥`` for the first and second projections, resp.  Consequently, if ``S : Signature 𝓞 𝓥`` is a signature, then

  ``∣ S ∣`` will denote the set of operation symbols (which we sometimes call ``F``), and

  ``∥ S ∥`` denotes the arity function (which we sometimes call ``ρ``).

Thus, if  ``𝓸 : ∣ S ∣``  is an operation symbol in the signature ``S``, then ``∥ S ∥ 𝓸`` denotes the arity of ``𝓸``.


-----------------------------------

.. _algebras in agda:

Algebras in Agda
------------------

Finally, we are ready to define the type of algebras in the signature ``S`` (which we also call "S-algebras").

::

   Algebra : (𝓤 : Universe) → {𝓞 𝓥 : Universe}
    →        (S : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
   Algebra 𝓤 {𝓞}{𝓥} S = Σ A ꞉ 𝓤 ̇ , ((𝓸 : ∣ S ∣) → Op (∥ S ∥ 𝓸) A)

Thus, algebras in the signature ``S`` (or `S``-algebras) inhabit the type ``Algebra 𝓤 {𝓞}{𝓥} S``. (Here, ``𝓤`` is the universe level of the type of carriers (or "universes") of ``S``-algebras.)

As an alternative to this syntax---one that may seem more in line with the standard literature---we could write the last line above as

.. code-block::

   Algebra 𝓤 {𝓞} {𝓥} (F , ρ) = Σ A ꞉ 𝓤 ̇ ,  ( (𝓸 : F )  → Op ( ρ 𝓸) A )

Here ``S = (F , ρ)`` is the signature with ``F`` the set of operation symbols and ``ρ`` the arity function.

Throughout the library, we adopt the (less standard, but more convenient) notations ``𝓸 : ∣ S ∣`` for an operation symbol of the signature ``S``, and ``∥ S ∥ 𝓸`` for the arity of that symbol.

Example
~~~~~~~~~~

A monoid signature has two operation symbols, say, ``e``  and ``·``, of arities 0 and 2 (thus, of types ``(𝟘 → A) → A`` and ``(𝟚 → A) → A``), resp.

::

   data monoid-op : 𝓤₀ ̇ where
    e : monoid-op
    · : monoid-op

   monoid-sig : Signature _ _
   monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }


The types indicate that ``e`` is nullary (i.e., takes no arguments, equivalently, takes args of type ``𝟘 → A``), while ``·`` is binary (as indicated  by argument type ``𝟚 → A``).

We will have more to say about the type of algebras later.  For now, we continue defining the syntax used in the ``agda-ualib`` to represent the basic objects of universal algebra.


-----------------------------------


Products of algebras in Agda
------------------------------

The (indexed) product of a collection of algebras is also an algebra if we define such a product as follows:

::

   module _ {S : Signature 𝓞 𝓥}  where

    Π' : {I : 𝓘 ̇}( A : I → Algebra 𝓤 S ) → Algebra (𝓤 ⊔ 𝓘) S
    Π' A =  (( ᵢ : _) → ∣ A ᵢ ∣) ,  λ 𝓸 x ᵢ → ∥ A ᵢ ∥ 𝓸 λ 𝓥 → x 𝓥 ᵢ

We have used an anonymous module here so that the (fixed) signature ``S`` is available in the definition of the product without mentioning it explicitly.


-----------------------------------------------


.. include:: hyperlink_references.rst
