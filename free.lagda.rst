.. File: free.lagda.rst
.. Author: William DeMeo  <williamdemeo@gmail.com>
.. Date: 25 Dec 2019
.. Updated: 29 Jan 2020
.. Note: This was used for the second part of my talk at JMM Special Session.
.. Copyright (c) 2019 William DeMeo

.. _Datatypes for Terms:

Datatypes for Terms 
======================

(The code described in this chapter resides in ``free.agda``.)

As usual, we begin by setting some options and importing a few things from the Agda std lib (as well as our definitions from the ``basic.agda`` file).

.. code-block:: agda
		
    {-# OPTIONS --without-K --exact-split #-}

    open import Level
    open import basic 
    open algebra
    open signature

    module free {S : signature}{X : Set} where

    open import preliminaries  using (_⊎_ ; ∀-extensionality; ∑)
    open import Function using (_∘_)
    open import Relation.Unary
    open import Relation.Binary hiding (Total)
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; sym)
    open Eq.≡-Reasoning
    import Relation.Binary.EqReasoning as EqR



-----------------------------------------------

Terms
-----------

We define the inductive family of terms in ``signature S`` as follows: 


.. code-block:: agda
		
    data Term : Set where

      generator : X -> Term

      node : ∀ (𝓸 : ⟨ S ⟩ₒ)
        ->   (Fin (⟨ S ⟩ₐ 𝓸) -> Term)
            -------------------------
	->    Term


-----------------------------------------------

The term algebra
-----------------

Here is a datatype for the term algebra in ``signature S``.

.. code-block:: agda
		
    open Term

    free : algebra S

    free = record { ⟦_⟧ᵤ = Term ; _⟦_⟧ = node }


-----------------------------------------------

The universal property
-----------------------------------

We now come to our first proof.

We wish to show that the term algebra is **aboslutely free**.

That is, we must show

1. every ``h : X -> ⟦ A ⟧ᵤ`` lifts to a hom from ``free`` to ``A``;

2. the induced hom is unique.


Here is the Agda code proving these facts.

1.
   a. Every map  ``(X -> A)``  "lifts".

      .. code-block:: agda
		
          free-lift : {A : algebra  S}
	              (h : X -> ⟦ A ⟧ᵤ)
                    ---------------------
            ->        ⟦ free ⟧ᵤ -> ⟦ A ⟧ᵤ

          free-lift h (generator x) = h x

          free-lift {A} h (node 𝓸 args) = (A ⟦ 𝓸 ⟧) λ{i -> free-lift {A} h (args i)}


   b. The lift is a hom.

      .. code-block:: agda
		
          open Hom

          lift-hom : {A : algebra S}
	             (h : X -> ⟦ A ⟧ᵤ)
                    ------------------
	    ->        Hom free A

          lift-hom {A} h =
            record
            {
              ⟦_⟧ₕ = free-lift {A} h;
              homo = λ args -> refl
            }


2. The lift to  ``(free -> A)``  is unique.

   N.B. we need function extensionality for this, which we import from our util.agda file (see the ``agda-ualib`` gitlab repository).

   .. code-block:: agda

       free-unique : {A : algebra S}
         ->    ( f g : Hom free A )
         ->    ( ∀ x  ->  ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x) )
         ->    (t : Term)
              ---------------------------
         ->    ⟦ f ⟧ₕ t ≡ ⟦ g ⟧ₕ t

       free-unique {A} f g p (generator x) = p x

       free-unique {A} f g p (node 𝓸 args) =
          begin
            ⟦ f ⟧ₕ (node 𝓸 args)
          ≡⟨ homo f args  ⟩
            (A ⟦ 𝓸 ⟧) (λ i -> ⟦ f ⟧ₕ (args i))
          ≡⟨ cong ((A ⟦_⟧)_) (∀-extensionality (induct f g p args)) ⟩
            (A ⟦ 𝓸 ⟧) (λ i -> ⟦ g ⟧ₕ (args i))
          ≡⟨ sym (homo g args) ⟩
            ⟦ g ⟧ₕ (node 𝓸 args)
          ∎
          where
           induct : {A : algebra S}
             ->     (f g : Hom free A)
             ->     (∀ x -> ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x))
             ->     (args : Fin (⟨ S ⟩ₐ 𝓸) → Term)
             ->     (i : Fin (⟨ S ⟩ₐ 𝓸))
                   --------------------------------------- (IH)
             ->     ⟦ f ⟧ₕ (args i) ≡ ⟦ g ⟧ₕ (args i)
           induct f' g' h' args' i' = free-unique f' g' h' (args' i')


   Now that we have see where and how induction is used, let's clean up the proof by inserting the induction step within the angle brackets inside the calculational proof.

   .. code-block:: agda

       free-unique : {A : algebra S}
         ->    ( f g : Hom free A )
         ->    ( ∀ x  ->  ⟦ f ⟧ₕ (generator x) ≡ ⟦ g ⟧ₕ (generator x) )
         ->    (t : Term)
              ---------------------------
         ->    ⟦ f ⟧ₕ t ≡ ⟦ g ⟧ₕ t

       free-unique {A} f g p (generator x) = p x

       free-unique {A} f g p (node 𝓸 args) =
          begin
	    ⟦ f ⟧ₕ (node 𝓸 args)
	  ≡⟨ homo f args  ⟩
	    (A ⟦ 𝓸 ⟧) (λ i -> ⟦ f ⟧ₕ (args i))
	  ≡⟨ cong ((A ⟦_⟧)_)
	     ( ∀-extensionality λ i -> free-unique f g p (args i) ) ⟩
	    (A ⟦ 𝓸 ⟧) (λ i -> ⟦ g ⟧ₕ (args i))
	  ≡⟨ sym (homo g args) ⟩
	    ⟦ g ⟧ₕ (node 𝓸 args)
	  ∎


-------------------------------------------------------

Due to time constraints, this is as far as I got during my JMM lecture.

Please check the web site `ualib.org <https://ualib.org>`_ for more information.

(As of 23 Jan 2020, the ualib.org website is outdated.  We plan to remedy this by early February 2020, and  update the site with links to the latest version of the Agda Universal Algebra Library, as well as documentation describing the library in great detail.)

-----------------------------------------------

.. include:: hyperlink_references.rst

