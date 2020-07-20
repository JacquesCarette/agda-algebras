.. FILE: birkhoff.lagda.rst
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 23 Feb 2020
.. UPDATE: 27 Jun 2020
.. REF: Based on the file `birkhoff.agda` (23 Jan 2020).

.. _birkhoffs theorem in agda:

============================
Birkhoff's Theorem in Agda
============================

Here we give a formal proof in Agda of :ref:`Birkhoff's theorem <birkhoffs theorem>` (:numref:`%s <birkhoffs theorem>`), which says that a variety is an equational class. In other terms, if a class 𝒦 of algebras is closed under the operators 𝑯, 𝑺, 𝑷, then 𝒦 is an equational class (i.e., 𝒦 is the class of algebras that model a particular set of identities).  The sections below contain (literate) Agda code that formalizes each step of the (informal) proof we saw above in :numref:`birkhoffs theorem`.

Preliminaries
-----------------

As usual, we start with the imports we will need below.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import prelude
  open import basic using (Signature; Algebra; Π'; _̂_)
  open import relations using (ker-pred; Rel; con; _//_)
  open import homomorphisms using (hom; is-homomorphism)
  open import closure using (VClo)
  open import terms using (Term; generator; 𝑻; _̇_; comm-hom-term;
                           lift-hom; interp-prod)

  open import subuniverses using (Subuniverse; mksub; var; app; Sg; Subalgebra)

.. _the birkhoff module:

The Birkhoff module
----------------------

We start the ``birkhoff`` module with a fixed signature and a type ``X``.  As in the ``terms`` module, ``X`` represents an arbitrary (infinite) collection of "variables" (which will serve as the generators of the :term:`term algebra` 𝑻(X)).

::

  module birkhoff {S : Signature 𝓞 𝓥} {X : 𝓧 ̇ }  where

.. _obs 1 in agda:

Equalizers
~~~~~~~~~~~~~~

The equalizer of two functions (resp., homomorphisms) ``g h : A → B`` is the subset of ``A`` on which the values of the functions ``g`` and ``h`` agree.  We formalize this notion in Agda as follows.

::

  --Equalizers of functions
  𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (g h : A → B) → Pred A 𝓦
  𝑬 g h x = g x ≡ h x

  --Equalizers of homomorphisms
  𝑬𝑯 : {A B : Algebra 𝓤 S} (g h : hom A B) → Pred ∣ A ∣ 𝓤
  𝑬𝑯 g h x = ∣ g ∣ x ≡ ∣ h ∣ x
  --cf. definition 𝓔 in the homomorphisms module

It turns out that the equalizer of two homomorphisms is closed under the operations of ``A`` and is therefore a subalgebra of the common domain, as we now prove.

::

  𝑬𝑯-is-closed : funext 𝓥 𝓤
   →      {𝑓 : ∣ S ∣ } {A B : Algebra 𝓤 S}
          (g h : hom A B)  (𝒂 : (∥ S ∥ 𝑓) → ∣ A ∣)
   →      ((x : ∥ S ∥ 𝑓) → (𝒂 x) ∈ (𝑬𝑯 {A = A}{B = B} g h))
          --------------------------------------------------
   →       ∣ g ∣ (∥ A ∥ 𝑓 𝒂) ≡ ∣ h ∣ (∥ A ∥ 𝑓 𝒂)

  𝑬𝑯-is-closed fe {𝑓 = 𝑓}{A = A , Fᴬ}{B = B , Fᴮ}
   (g , ghom)(h , hhom) 𝒂 p =
     g (Fᴬ 𝑓 𝒂)    ≡⟨ ghom 𝑓 𝒂 ⟩
     Fᴮ 𝑓 (g ∘ 𝒂)  ≡⟨ ap (Fᴮ _ )(fe p) ⟩
     Fᴮ 𝑓 (h ∘ 𝒂)  ≡⟨ (hhom 𝑓 𝒂)⁻¹ ⟩
     h (Fᴬ 𝑓 𝒂)    ∎

Thus, ``𝑬𝑯`` is a subuniverse of ``A``.

::

  -- Equalizer of homs is a subuniverse.
  𝑬𝑯-is-subuniverse : funext 𝓥 𝓤
   →  {A B : Algebra 𝓤 S}(g h : hom A B) → Subuniverse {A = A}
  𝑬𝑯-is-subuniverse fe {A = A} {B = B} g h =
   mksub (𝑬𝑯 {A = A}{B = B} g h)
    λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {A = A} {B = B} g h 𝒂 x

.. _obs 3 in agda:

Homomorphisms
~~~~~~~~~~~~~~

The :numref:`homomorphisms module (Section %s) <homomorphisms module>` formalizes the notion of homomorphism and proves some basic facts about them. Here we show that homomorphisms are determined by their values on a generating set, as stated and proved informally in :numref:`Obs %s <obs 3>`.  This is proved here, and not in :numref:`homomorphisms module`, because we need ``Sg`` from the ``subuniverses`` module (see :numref:`subuniverses in agda`).

::

  HomUnique : funext 𝓥 𝓤 → {A B : Algebra 𝓤 S}
             (X : Pred ∣ A ∣ 𝓤)  (g h : hom A B)
   →         (∀ (x : ∣ A ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
           ---------------------------------------------------
   →        (∀ (a : ∣ A ∣) → a ∈ Sg {A = A} X → ∣ g ∣ a ≡ ∣ h ∣ a)

  HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x
  HomUnique fe {A = A , Fᴬ}{B = B , Fᴮ} X
   (g , ghom) (h , hhom) gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
    g (Fᴬ 𝑓 𝒂)     ≡⟨ ghom 𝑓 𝒂 ⟩
    Fᴮ 𝑓 (g ∘ 𝒂 )   ≡⟨ ap (Fᴮ 𝑓) (fe induction-hypothesis) ⟩
    Fᴮ 𝑓 (h ∘ 𝒂)    ≡⟨ ( hhom 𝑓 𝒂 )⁻¹ ⟩
    h ( Fᴬ 𝑓 𝒂 )   ∎
   where
    induction-hypothesis =
      λ x → HomUnique fe {A = A , Fᴬ}{B = B , Fᴮ} X
      (g , ghom)(h , hhom) gx≡hx (𝒂 x) ( im𝒂⊆SgX x )

**Obs**. If 𝐴, 𝐵 are finite and 𝑋 generates A, then ∣Hom(A, B)∣ ≤ :math:`∣B∣^{∣X∣}`.
Proof. By ``HomUnique``, a homomorphism is uniquely determined by its restriction to a generating set. If 𝑋 generates A, then since there are exactly :math:`∣B∣^∣X∣` functions from 𝑋 to 𝐵, the result holds. □

.. todo:: formalize **Obs**.

.. _obs 14 in agda:

Identities preserved by homs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recall (:numref:`Obs %s <obs 14>`) that an identity is satisfied by all algebras in a class if and only if that identity is compatible with all homomorphisms from the term algebra 𝑻(X) into algebras of the class.  More precisely, if𝓚 is a class of 𝑆-algebras and 𝑝, 𝑞 terms in the language of 𝑆, then,

.. math:: 𝒦 ⊧ p ≈ q \; ⇔ \; ∀ A ∈ 𝒦, ∀ h ∈ \mathrm{Hom}(𝑻(X), A), h ∘ p^𝑻(X) = h ∘ q^𝑻(X).

We now formalize this result in Agda. First, we define the syntax for ``⊧``.


::

  module _
   (𝓚 : Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺)))
   -- {UV : Univalence}
   {X : 𝓤 ̇ }
   (gfe : global-dfunext)
   -- (dfe : dfunext 𝓤 𝓤)
   where


   -- Duplicating definition of ⊧ so we don't have to import from closure module.
   -- (Remove these definitions later once closure module is working.)
   _⊧_≈_ : Algebra 𝓤 S
    →      Term{X = X} → Term → 𝓤 ̇

   A ⊧ p ≈ q = (p ̇ A) ≡ (q ̇ A)

   _⊧_≋_ : Pred (Algebra 𝓤 S) 𝓦
    →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇

   _⊧_≋_ 𝓚 p q = {A : Algebra _ S} → 𝓚 A → A ⊧ p ≈ q


   -- ⇒ (the "only if" direction)
   identities-are-compatible-with-homs : (p q : Term{X = X})
    →                𝓚 ⊧ p ≋ q
         ----------------------------------------------------
    →     ∀ A KA h → ∣ h ∣ ∘ (p ̇ 𝑻(X)) ≡ ∣ h ∣ ∘ (q ̇ 𝑻(X))
   -- Here, the inferred types are
   -- A : Algebra 𝓤 S, KA : 𝓚 A, h : hom (𝑻(X){X = X}) A

   identities-are-compatible-with-homs p q 𝓚⊧p≋q A KA h = γ
    where
     pA≡qA : p ̇ A ≡ q ̇ A
     pA≡qA = 𝓚⊧p≋q KA

     pAh≡qAh : ∀(𝒂 : X → ∣ 𝑻(X) ∣)
      →        (p ̇ A)(∣ h ∣ ∘ 𝒂) ≡ (q ̇ A)(∣ h ∣ ∘ 𝒂)
     pAh≡qAh 𝒂 = intensionality pA≡qA (∣ h ∣ ∘ 𝒂)

     hpa≡hqa : ∀(𝒂 : X → ∣ 𝑻(X) ∣)
      →        ∣ h ∣ ((p ̇ 𝑻(X)) 𝒂) ≡ ∣ h ∣ ((q ̇ 𝑻(X)) 𝒂)
     hpa≡hqa 𝒂 =
      ∣ h ∣ ((p ̇ 𝑻(X)) 𝒂)  ≡⟨ comm-hom-term gfe (𝑻(X)) A h p 𝒂 ⟩
      (p ̇ A)(∣ h ∣ ∘ 𝒂) ≡⟨ pAh≡qAh 𝒂 ⟩
      (q ̇ A)(∣ h ∣ ∘ 𝒂) ≡⟨ (comm-hom-term gfe (𝑻(X)) A h q 𝒂)⁻¹ ⟩
      ∣ h ∣ ((q ̇ 𝑻(X)) 𝒂)  ∎

     γ : ∣ h ∣ ∘ (p ̇ 𝑻(X)) ≡ ∣ h ∣ ∘ (q ̇ 𝑻(X))
     γ = gfe hpa≡hqa

   -- ⇐ (the "if" direction)
   homs-are-compatible-with-identities : (p q : Term)
    →    (∀ A KA h  →  ∣ h ∣ ∘ (p ̇ 𝑻(X)) ≡ ∣ h ∣ ∘ (q ̇ 𝑻(X)))
         -----------------------------------------------
    →                𝓚 ⊧ p ≋ q
   --Inferred types: A : Algebra 𝓤 S, KA : A ∈ 𝓚, h : hom 𝑻(X) A

   homs-are-compatible-with-identities p q all-hp≡hq {A = A} KA = γ
    where
     h : (𝒂 : X → ∣ A ∣) → hom (𝑻(X)) A
     h 𝒂 = lift-hom{A = A} 𝒂

     γ : A ⊧ p ≈ q
     γ = gfe λ 𝒂 →
      (p ̇ A) 𝒂
        ≡⟨ refl _ ⟩
      (p ̇ A)(∣ h 𝒂 ∣ ∘ generator)
        ≡⟨(comm-hom-term gfe (𝑻(X)) A (h 𝒂) p generator)⁻¹ ⟩
      (∣ h 𝒂 ∣ ∘ (p ̇ 𝑻(X))) generator
        ≡⟨ ap (λ - → - generator) (all-hp≡hq A KA (h 𝒂)) ⟩
      (∣ h 𝒂 ∣ ∘ (q ̇ 𝑻(X))) generator
        ≡⟨ (comm-hom-term gfe (𝑻(X)) A (h 𝒂) q generator) ⟩
      (q ̇ A)(∣ h 𝒂 ∣ ∘ generator)
        ≡⟨ refl _ ⟩
      (q ̇ A) 𝒂
        ∎

   compatibility-of-identities-and-homs : (p q : Term)
    →  (𝓚 ⊧ p ≋ q)
        ⇔ (∀ A KA hh → ∣ hh ∣ ∘ (p ̇ 𝑻(X)) ≡ ∣ hh ∣ ∘ (q ̇ 𝑻(X)))
   --inferred types: A : Algebra 𝓤 S, KA : A ∈ 𝓚, hh : hom 𝑻(X) A.

   compatibility-of-identities-and-homs p q =
     identities-are-compatible-with-homs p q ,
     homs-are-compatible-with-identities p q

   TH : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) → _ ̇
   TH 𝒦 = Σ (p , q) ꞉ (Term{X = X} × Term) , 𝒦 ⊧ p ≋ q

   Th : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) → Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
   Th 𝒦 = λ (p , q) → 𝒦 ⊧ p ≋ q

   MOD : Pred (Term{X = X} × Term) 𝓤 → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⁺) ̇
   MOD Σ' = Σ 𝑨 ꞉ (Algebra 𝓤 S) , ∀ p q → (p , q) ∈ Σ' → 𝑨 ⊧ p ≈ q

   Mod : Pred (Term{X = X} × Term) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ) → Pred (Algebra 𝓤 S)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ )
   Mod Σ' = λ 𝑨 → ∀ p q → (p , q) ∈ Σ' → 𝑨 ⊧ p ≈ q

   --Birkhoff's theorem: every variety is an equational class.
   -- birkhoff : (𝒦 : Pred (Algebra 𝓤 S)(𝓤 ⁺))
   --            (𝑨 : Algebra 𝓤 S)(g : X → ∣ 𝑨 ∣ )(eg : Epic g)
   --  →         (𝑨 ∈ (Mod (Th (VClo 𝒦)))) → 𝑨 ∈ VClo 𝒦
   -- birkhoff 𝒦 𝑨 g eg A∈ModThV = γ
   --  where
   --   h : hom (𝑻 X) 𝑨
   --   h = lift-hom{𝑨 = 𝑨}{X = X} g

   --   γ : 𝑨 ∈ VClo 𝒦
   --   γ = {!!}

------------------

.. include:: hyperlink_references.rst

