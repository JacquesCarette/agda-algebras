.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _algebraic-preliminaries:

=============================
Algebraic Preliminaries
=============================

.. index:: operation, arity, image
.. index::
   symbol: ℕ
   symbol: ̱m  

.. _operations:

Operations
----------

The symbols ℕ, ω, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If :math:`m` is a natural number, we write :math:`m : ℕ` and say ":math:`m` has type ℕ." [1]_

For :math:`m : ℕ`, denote and define :math:`\underline m := \{0, 1, \dots, m-1\}`.

Let :math:`a[\underline m] = (a_0, a_1, \dots, a_{m-1})` denote the :ref:`mtuple <tuple-functors>` of elements :math:`a_i : A`, for each :math:`i : \underline m`.

The :ref:`mtuple <tuple-functors>` :math:`a[\underline m]` may be identified with the function :math:`a : \underline m → A`, where :math:`a(i) = a_i`, for each :math:`i : \underline m`. (See :numref:`Section %s <general-composition>` for a discussion of this identification.)

If :math:`h  : A → A`, then :math:`h ∘ a : \underline m → A` is the function whose :math:`i`-th coordinate is

.. math:: (h ∘ a)(i) = h(a(i)) = h(a_i), 

and we may formally identify the function :math:`h ∘ a : \underline m → A` with its image---that is, the **image of** :math:`\underline m` **under** :math:`h ∘ a`---which is the :ref:`mtuple <tuple-functors>`,

.. math:: (h ∘ a)[\underline m] = (h(a_0), h(a_1), \dots, h(a_{m-1})).

.. index:: signature

.. _signatures:

Signatures
----------

Classically, a **signature** :math:`σ = (F, ρ)` consists of a set :math:`F` of operation symbols and a function :math:`ρ : F → ℕ`.

For each operation symbol :math:`f ∈ F`, the value :math:`ρf` is the **arity** of :math:`f`. (Intuitively, the arity can be thought of as the "number of arguments" that :math:`f` takes as "input".)

If :math:`A` is a set and :math:`f` is a :math:`ρf`-ary function on :math:`A`, then we often write :math:`f : A^{ρf} → A` to indicate this.

On the other hand, the arguments of such a function form a :math:`ρf`-tuple, :math:`(a_0, a_1, \dots, a_{ρf -1})`, which may be viewed as the graph of the function :math:`a : ρf → A`, where :math:`a(i) = a_i`.

Thus, by identifying the :math:`ρf`-th power :math:`A^{ρf}` with the type :math:`ρf → A` of functions from :math:`\{0, 1, \dots, ρf -1\}` to :math:`A`, we identify the function type :math:`A^{ρf} → A` with the (functional) type :math:`(ρf → A) → A`. [2]_

.. proof:example::

   Suppose 

     :math:`g : (\underline m → A) → A` is an :math:`\underline m`-ary operation on :math:`A`, and 
   
     :math:`a : \underline m → A` is an :math:`m`-tuple on :math:`A`.

   Then :math:`g a = g(a_0, a_1, \dots, a_{m-1})` has type :math:`A`.

   Suppose

     :math:`f : (ρf → B) → B` is a :math:`ρf`-ary operation on :math:`B`,

     :math:`a : ρf → A` is a :math:`ρf`-tuple on :math:`A`, and

     :math:`h : A → B`.
      
   Then :math:`h ∘ a : ρf → B` and :math:`f (h ∘ a) : B`.

It is important to be familiar with the classical notions of signature and arity, since these are used by almost all algebraists. However, in :numref:`Section %s <f-algebra>` we give alternative, category theoretic definitions of these things that are sometimes easier to compute with.

.. index:: triple: algebra; structure; universal algebra

.. _algebras:

Algebras
--------

An **algebraic structure** is denoted by :math:`𝔸 = ⟨ A, F^𝔸⟩` and consists of 

  #. :math:`A` := a set, called the *carrier* (or *universe*) of the algebra,
  #. :math:`F^𝔸 = \{ f^𝔸 ∣ f ∈ F, \ f^𝔸 : (ρf → A) → A \}` := a set of operations on :math:`A`,
  #. a collection of identities satisfied by elements of :math:`A` and operations in :math:`F^𝔸`.

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :cat:`Set`, such as multisorted algebras, and higher-type universal algebra :cite:`MR2757312`, :cite:`MR3003214`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`MR1173632`). These are natural generalizations that we will incorporate in our development later. (See :numref:`Section %s <postmodern-algebra>`.) But our first goal is to develop a working library for classical (single-sorted, set-based) universal algebra. 

---------------------------

.. _homomorphisms:

Homomorphisms
--------------

Let :math:`𝔸 = ⟨ A, F^𝔸 ⟩` and :math:`𝔹 = ⟨ B, F^𝔹 ⟩` be algebras of the same signature, and let :math:`φ : A → B` be a function. Take an :math:`n`-ary operation symbol :math:`f ∈ F`, and suppose that for all :math:`a_1, \dots a_{n} ∈ A` the following equation holds:

.. math:: φ (f^𝔸 (a_1, \dots, a_{n})) = f^𝔹 (φ (a_1), \dots, φ (a_{n})).

Then :math:`φ` is said to **respect the interpretation of** :math:`f`. If :math:`φ` respects the interpretation of every :math:`f ∈ F`, then we call :math:`φ` a **homomorphism** from 𝔸 to 𝔹, and we write :math:`φ \in \operatorname{Hom}(𝔸, 𝔹)`, or simply, :math:`φ : 𝔸 → 𝔹`.

.. .. proof:observation::
..  For groups, to check that a map :math:`φ : G → H` is a homomorphism, it is enough to check that :math:`φ` respects the interpretation of the binary operation. It follows from this that such a function respects the unary and nulary operations as well.

---------------------------------

Epis, Monos, and Autos
-----------------------

.. todo:: complete this section

.. proof:definition:: Notation for homs, epis, monos, and autos

   If :math:`𝔸 = ⟨A, f^𝔸⟩` and :math:`𝔹 = ⟨B, f^𝔹⟩` are algebras, we denote and define

   + :math:`\hom(𝔸, 𝔹) =` homomorphisms from 𝔸 to 𝔹.
   + :math:`\epi(𝔸, 𝔹) =` epimorphisms from 𝔸 onto 𝔹.
   + :math:`\mono(𝔸, 𝔹) =` monomorphisms from 𝔸 into 𝔹.
   + :math:`\aut(𝔸, 𝔹) =` automorphisms from 𝔸 into and onto 𝔹.

------------------------------

.. rubric:: Footnotes

.. [1]
   For a brief and gentle introduction to type theory see the `section on axiomatic foundations <https://leanprover.github.io/logic_and_proof/axiomatic_foundations.html?highlight=type#type-theory>`_ in `Logic and Proof <https://leanprover.github.io/logic_and_proof/>`_.  Alternatively, viewing :math:`m  : \mathbb N` as roughly equivalent to :math:`n\in \mathbb N` is not totally unreasonable at this point.

.. [2]
   By "functional" we mean a function whose domain is a collection of functions.

.. _categorytheory.gitlab.io: https://categorytheory.gitlab.io

.. _Lean: https://leanprover.github.io/
