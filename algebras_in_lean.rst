.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _algebras-in-lean:

================
Algebras in Lean
================

This section demonstrates the utility of dependent and inductive types by expressing some fundamental concepts of universal algebra in Lean.

In particular, we will formally represent each of the following:  *operation*, *algebra*, *subuniverse*, and *term algebra*.

Our formal representations of these concepts will be clear, concise, and computable. Moreover, we strive to develop a notation and syntax that will feel natural to working algebraists.

Our goal here is to demonstrate the power of Lean's type system for expressing mathematical concepts precisely and constructively, and to show that if we make careful design choices at the start of our development, then our formal theorems *and their proofs* can approximate the efficiency and readability of analogous informal presentations found in the mathematics literature.

Most of the Lean code described in this section can be found in the files ``basic.lean`` and ``subuniverse.lean`` which reside in the ``src`` directory of the lean-ualib_ repository.

.. index:: arity, operation
.. index:: airty type, operation symbol type
.. index:: type of; operation symbols
.. index:: type of; arities
.. index:: type of; natural numbers

----------------------------------------

.. _operations-in-lean:

Operations in Lean
-------------------

Recall, the symbols ℕ, ω, and ``nat`` are synonymous and all denote the **type of natural numbers**.

We start with the **type of operation symbols**, which depends on our semantic notion of **arity**, also captured by a type.

Argument lists that are passed to operations are represented by tuples which are simply functions, say, of type β → α, where β is the **arity type** of the operation to which the tuple will be passed as an argument list.

Heuristically, it's fine to think of | β | as the "number" of arguments the operation takes, but the implementation is much more general than that. In particular, there is no reason to restrict the arity type to be a finite set, *a priori*.

.. index:: ! type of; operations

An **operation** takes a tuple (or, list of "arguments") of type β → α and returns an element of type α.  Here, α is the type on which the operation is defined.

In the lean-ualib_, given types α and β, we define the type of **β-ary operations on α** to be (β → α) → α, and we denote this type by ``op (β α)``.

.. code-block:: lean

   -- operation type
   definition op (β α) := (β → α) → α

.. index:: ! projection function

A simple but important example of an operation of type ``op (β α)`` is the **β-ary projection on α**, which is defined as follows:

.. code-block:: lean

   -- operation type
   definition op (β α) := (β → α) → α

   -- BEGIN
   -- Example Operation (Projection)
   -- Get i-th element of a given tuple ``a``.
   definition π {β α} (i) : op β α := λ a, a i
   -- END

For clarity, it is sometimes helpful to make the types explicit, so we repeat the definition of the β-ary projection on α, this time showing the types.

.. code-block:: lean

   -- operation type
   definition op (β α) := (β → α) → α

   -- BEGIN
   -- (same example but with types shown explicitly)
   definition π {β α} (i : β) : op β α := λ (a : β → α), a i
   -- END

The operation ``π i`` maps a given tuple ``a: β → α`` to its "value" ``a i`` at input ``i``.

For instance, if we have types ``α`` and ``β``, and inhabitants ``i: β`` and ``a: β → α``, then the command ``#check π i a`` shows that the type of ``π i a`` is ``α``, as expected, since ``π i a = a i``.

.. code-block:: lean

   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ a, a i

   -- BEGIN
   section Example_operation_projection
     parameters (α : Type*) (β : Type*) (i : β) (a : β → α) 
     #check π i a
   end Example_operation_projection
   -- END

Here are a couple of examples that are a bit more concrete.

.. code-block:: lean

   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ a, a i

   -- BEGIN
   -- Example: the tuple p1 = (1, 2, 3, ...).
   definition p1 : ℕ → ℕ := λ n, n+1

   -- What's the 3rd projection of p1?
   #eval π 3 p1                         -- answer: 4

   -- Example: the constant tuple sevens = (7, 7, 7, ...)
   definition sevens : ℕ → ℕ := λ n, 7

   -- What's the 3rd projection of sevens?
   #eval π 3 sevens                      -- answer: 7
   -- END

.. index:: ! signature, ! operation symbol, ! similarity type
.. index:: ! arity

----------------------------------------------------------

.. _signatures-in-lean:

Signatures in Lean
------------------

A **signature** :math:`σ = (F, ρ)` consists of

  + a set :math:`F` of **operation symbols**, and
  + a **similarity type** :math:`ρ: F → β`.
  
For each operation symbol :math:`f : F`, the value :math:`ρ f` is the **arity** of :math:`f`.  This value has type :math:`β`, which is the **arity type**.

In classical universal algebra we typically assume that :math:`β = ℕ`, but for much of the basic theory this choice is inconsequential. [1]_

.. index:: ! type of; signatures
.. index:: ! type of; operations
.. index:: ! arity function

We now implement a type of signatures and a type of operations in Lean_.  In the process we compare and contrast the formal and the informal presentations of these concepts.

Define the **type of signatures** as a structure with two fields, the type ``F`` of operation symbols, and an **arity function** ``ρ : F → Type*``, which takes each operation symbol ``f`` to its arity ``ρ f``.

.. code-block:: lean

   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ a, a i

   -- BEGIN
   -- signature type
   -- F : a set of operation symbols
   -- ρ : returns the arity of a given operation symbol
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   -- END

.. index:: ! type of; interpretations of operations
.. index:: keyword: section
.. index:: keyword: local notation

In the next section, we define the **type of interpretations of operations** on the :index:`carrier type` ``α``.  Before proceeding, however, we note that by starting a new ``section`` we could define some parameters (such as a fixed signature ``σ``) that will be available throughout the section. [2]_

.. code-block:: lean

   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ a, a i
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   -- BEGIN
   section
     parameter (σ : signature)
     local notation `F` := σ.F
     local notation `ρ` := σ.ρ 
   end
    -- END

This enables us to define some ``local notation``, so that we can write ``f : F`` (instead of ``f : σ.F``) to indicate that the operation symbol ``f`` has type ``F``; similarly, for the arity of ``f``, we can write ``ρ f`` (instead of ``σ.ρ f``). This syntactic sugar results in Lean syntax that matches that of informal algebra almost exactly. [3]_ 

.. index:: pair: variety; equational class
.. index:: triple: algebra; structure; universal algebra
.. index:: carrier type

-------------------------------------------------------

.. _universal-algebras-in-lean:

Algebras in Lean
----------------

Classical universal algebra is the study of **varieties** (or **equational classes**) of algebraic structures.

A **universal algebra** (also known as an **algebraic structure**) is denoted by :math:`𝐀 = ⟨A, F^{𝐀}⟩` and consists of 

  + a set :math:`A`, called the **universe** (or **carrier**) of the algebra,
  + a set :math:`F^{𝐀} = \{f^{𝐀} ∣ f ∈ F, f^{𝐀} : (ρf → A) → A\}` of **operations** defined on :math:`A`, and
  + a collection of **identities** satisfied by the elements and operations of 𝐀.

Usually, the algebraic structures we study are **single-sorted**, meaning each structure has only one universe and that universe is of only a single type. Furthermore, in classical algebra, the universes are typically sets.

Some of the renewed interest in universal algebra has focused on representations of algebras in categories other than :math:`\mathbf{Set}`, such as **multisorted** algebras and higher-type algebras, etc. (:cite:`MR2757312`, :cite:`MR3003214`, :cite:`Finster:2018`, :cite:`Gepner:2018`, :cite:`MR1173632`). These are natural generalizations that will eventually be incorporated into ``lean-ualib``, but for now we content ourselves with developing and documenting an *accessible* implementation of the classical core of (single-sorted, set-based) universal algebra.

One arity to rule them all!
~~~~~~~~~~~~~~~~~~~~~~~~~~~

When working informally, we typically denote an :math:`n`-ary operation by, say, :math:`f(x_0, x_1, \dots, x_{n-1})`, the arguments appearing as an :math:`n`-tuple, :math:`(x_0, x_1, \dots, x_{n-1})`.  However, when computing with functions (and even when not!) this is impractical for a number of reasons.

Functional programming languages like Lean_ are based on the :term:`lambda calculus`.  One reason for this is that there is only one kind of type (the function type); moreoever, every function is a *unary* function.  This has a major advantage for computing: our code need not depend on the arity of a given function.

Representing an :math:`n`-ary function by a unary function can be done in a number of essentially equivalent ways.  One is by :term:`currying`.  Another is by viewing the :math:`n`-tuple (e.g., passed to an :math:`n`-ary function) as a function.  We take the latter approach here (though we will have plenty of opportunities to curry later).

So, let us review how the correspondence between tuples and functions works by way of an example. [4]_ Suppose :math:`A` is a set and :math:`f` is a :math:`ρ f`-ary operation on :math:`A`. In this case, we often write :math:`f : A^{ρf} → A`.

Let :math:`β` be the arity type. If :math:`β` happens to be ℕ, then :math:`ρ f = \{0, 1, \dots, ρf-1\}` and a function :math:`g : ρf → A` is simply a :math:`ρ f`-tuple of elements of :math:`A`. [5]_

Conversely, for :math:`m : ℕ`, an :math:`m`-tuple :math:`a = (a_0, a_1, \dots , a_{m-1}) : A^m` is (the graph of) the function :math:`a : m → A`, defined for each :math:`i < m` by :math:`a\,i = a_i`. 

If :math:`h : A → B` and :math:`a : m → A`, then :math:`h ∘ a : m → B` is the tuple whose :math:`i`-th value is :math:`(h ∘ a) i = h\, a\, i = h a_i`, which has type :math:`B`.

If :math:`g : A^m → A` and :math:`a : m → A`, then the value :math:`g\, a` has type :math:`A`.

Putting it all together, if

  + :math:`f : (ρf → B) → B` is a :math:`ρ f`-ary operation on :math:`B`, 
  + :math:`a : ρf → A` is a :math:`ρ f`-tuple on :math:`A`, and 
  + :math:`h : A → B`,

then :math:`h ∘ a : ρf → B` and :math:`f (h ∘ a) : B`.

.. index:: type of; interpretations of operations

The ``algebra_on`` type
~~~~~~~~~~~~~~~~~~~~~~~

Before defining a type of universal algebras, we first define a type called ``algebra_on`` which will be the **type of interpretations of operations** of a given signature. Our definition of ``algebra_on`` uses a :ref:`dependent function type <pi-type>` (or "Pi type").

Given a signature :math:`σ = (F, ρ)` and a carrier type :math:`α`, an inhabitant of ``algebra_on σ α`` is determined by assigning an interpretation to each operation symbol :math:`f : F`.  Such an interpretation is a function of type :math:`(ρ f → α) → α` (which *depends* on :math:`f`).

Thus, given a signature :math:`σ = (F, ρ)`, the ``algebra_on α`` type is

.. math:: \prod_{f : F} (ρ f → α) → α = \prod_{f : F} \mathrm{op} \,(ρ f)\, α.

.. code-block:: lean

   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ a, a i
   structure signature := mk :: (F : Type*) (ρ : F → Type*)

   -- BEGIN
   -- algebra_on type
   -- Define interpretations of operations on carrier type α
   definition algebra_on (σ : signature) (α : Type*) := 
   Π (f : σ.F), op (σ.ρ f) α   

      -- This is called `algebra_on` since an algebra is fully
      -- specified by its (Cayley) operation tables. An inhabitant 
      -- of `algebra_on` assigns to each op symbol f : F, of 
      -- arity `β = S.ρ f`, an interpretation of f, that is, 
      -- a function of type (β → α) → α.
   -- END

.. index:: Pi type

Since the :ref:`dependent function type <pi-type>` or "Pi type" (denoted ``pi`` or ``Π`` in Lean_) is among one of the most important types in dependent type theory, let us pause pause for a moment to discuss it.

The **Pi type** :math:`Π_(x:A), B x` is called a *dependent function type* because it generalizes the function type :math:`A → B` by allowing the type :math:`B x` of the codomain to depend on the *value* :math:`x : A` of the domain. (See :numref:`Section %s <dependent-types>` for more about dependent types.)
 
Here is how the type ``pi`` is defined in the Lean_ standard library.

.. todo:: check this!

.. code-block:: lean

    variables {α : Type*} {π : α → Type*}

    def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := 
    { f | ∀ a ∈ i, f a ∈ s a }

.. (See also :numref:`Appendix Section %s <pi-type>`, for a more technical description of Leans ``pi`` type.)

.. index:: type of; universal algebras

The (universal) ``algebra`` type
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Finally, let us define the **type of universal algebras** in Lean.

A :index:`universal algebra` :math:`𝐀 = ⟨A,F^𝐀⟩` is a pair consisting of a :index:`carrier` (or :index:`universe`) :math:`A` along with an set :math:`F^𝐀` of :index:`operations` (i.e., interpretations of the operation symbols in :math:`F`).

Also, we should have the concept of an algebraic structures of any given signature. Thus, the type of :math:`⟨A,F^𝐀⟩` depends on the choice of signature :math:`σ = (F, ρ)`, so it is natural to encode the type of algebras as a :index:`dependent pair`, or :index:`Sigma type`.

.. code-block:: lean

   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ a, a i
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   definition algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   

   -- BEGIN
   -- algebra type
   -- pairs a carrier with an interpretation of op symbols
   definition algebra (σ : signature) := sigma (algebra_on σ)

   -- sigma is the "dependent pair" type: ⟨α, β α⟩ 
   -- which is appropriate here since an algebra consists of 
   -- a universe (of type α), and operations on that universe,
   -- the type of the operations depends on the universe type.
   -- END

An algebra pairs a carrier with an interpretation of the op symbols.

.. index:: Sigma type

The type ``sigma`` is the Sigma type, which is also known as a :ref:`dependent pair <sigma-type>` (i.e., dependent product). It is one of the most important types in dependent type theory, so let's pause for a moment to discuss it.

The Sigma type :math:`Σ_(x:A), B x` is called a *dependent pair type* because it generalizes the Cartesian product :math:`A × B` by allowing the type :math:`B x` of the second component to depend on the *value* :math:`x` of the first.

Here is how the type ``sigma`` is defined in the Lean_ standard library.

.. code-block:: lean

   structure sigma {α : Type u} (β : α → Type v) :=
   mk :: (fst : α) (snd : β fst)

Sigma is the appropriate type for the ``algebra`` type since an algebra consists of a universe (of type α), along with operations on that universe, and the type of each operation is dependent on the universe type α.

Syntactic sugar and coersions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Lean_ has a nifty :index:`coersion` feature which we use for the following purpose: if ``A`` is an algebra, Lean_ will try to determine the correct type of the symbol A---either the algebra itself or the universe of the algebra---depending on the context (just as we would when working informally!).

The next bit of code shows how the ``has_coe_to_sort`` and ``has_coe_to_fun`` coersion directives direct Lean_ to yield either the universe of the algebra or the whole algebra, as appropriate for the given context.

.. code-block:: lean

   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ a, a i
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   definition algebra_on (σ : signature) (α : Type*) := Π (f : σ.F), op (σ.ρ f) α   
   definition algebra (σ : signature) := sigma (algebra_on σ)

   -- BEGIN
   instance alg_carrier (σ : signature) : has_coe_to_sort (algebra σ) := ⟨_, sigma.fst⟩
   instance alg_operations (σ : signature) : has_coe_to_fun (algebra σ) := ⟨_, sigma.snd⟩
   -- END

.. index:: keyword: has_coe_to_sort
.. index:: keyword: has_coe_to_fun
.. index:: coersion

.. The last two lines are tagged with ``has_coe_to_sort`` and ``has_coe_to_fun``, respectively, because here we are using a very nice feature of Lean called **coercions**.

Using coercions allows us to identify certain objects which, though not identical, are normally conflated in informal mathematics. 

For instance, the standard notation for the interpretation of the operation symbol :math:`f` in the algebra :math:`𝐀 = ⟨A, F^𝐀⟩` is :math:`f^𝐀`. In our Lean implementation, we use ``A f`` to denote :math:`f^𝐀`. Although this syntax doesn't match the informal syntax exactly, it seems equally elegant and adapting to it should not overburden the user.

See :numref:`Section %s <coercion>` for a simple example and the precise definitions of ``has_coe_to_sort`` and ``has_coe_to_fun`` in the Lean_ library.

-----------------------------------------------

.. index:: homomorphism

.. _homomorphisms-in-lean:

Homomorphisms in Lean
---------------------

Using the types defined in the last section, it's not hard to represent the assertion that a function :math:`h : A → B` is a :ref:`homomorphism <homomorphisms>`.

We could clean this up a bit by fixing the signature σ and algebras 𝐀 and 𝐁 in advance, the definition looks a bit cleaner.

.. code-block:: lean

   import data.set
   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ f, f i
   variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   section
     parameter (σ : signature)
     local notation `F` := σ.F
     local notation `ρ` := σ.ρ 
     definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   
     definition algebra := sigma algebra_on
     instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩
     instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
   end

   -- BEGIN
   variables {σ : signature} {A : algebra σ} {B : algebra σ}

   definition homomorphic (h : A → B) := ∀ f a, h (A f a) = B f (h ∘ a)
   -- END

Comparing this with a common informal language definition of a homomorphism, which is typically something similar to :math:`∀ f \ ∀ a \ h (f^𝐀 (a)) = f^𝐁 (h ∘ a)`, we expect working algebraists to find the ``lean-ualib`` syntax quite readable.

Alternatively, we could define ``homomorphic`` so that the signature and algebras are not specified in advance, but instead passed in as arguments. This is demonstrated below, along with a third alternative that makes the types explicit which can sometimes be instructive.

.. code-block:: lean

   import data.set
   definition op (β α) := (β → α) → α
   definition π {β α} (i) : op β α := λ f, f i
   variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
   structure signature := mk :: (F : Type*) (ρ : F → Type*)
   section
     parameter (σ : signature)
     local notation `F` := σ.F
     local notation `ρ` := σ.ρ 
     definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   
     definition algebra := sigma algebra_on
     instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩
     instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
   end

   -- BEGIN
   def homomorphic_with_args 
   {σ : signature} {A : algebra σ} {B : algebra σ} 
   (h : A → B) := ∀ f a, h (A f a) = B f (h ∘ a)

   def homomorphic_explicit (h : A → B) := 
   ∀ (f : σ.F) (a : σ.ρ f → A.fst), h (A f a) = B f (h ∘ a)
   -- END

--------------------------------------------------------------

.. rubric:: Footnotes

.. [1]
   As we will see when implementing general operations in Lean, it is unnecessary to commit in advance to a specific arity type :math:`N`. An exception is the *quotient algebra type* since, unless we restrict ourselves to finitary operations, lifting a basic operation to a quotient requires some form of choice.

.. [2]
   The  ``section`` command allows us to open a section throughout which our signature ``σ`` will be available; ``section`` ends when the keyword ``end`` appears.

.. [3]
   The only exception is that in type theory we make *typing judgments*, denoted by ``:``, rather than set membership judgments, denoted by ``∈``.

.. [4]
   For a more general and detailed treatment of this topic, see :numref:`Section %s <tuple-functors>`.

.. [5]
   Technically, this assumes we identify :math:`g` with its graph, which is fairly common practice. We will try to identify any situations in which the conflation of a function with its graph might cause problems.

.. _Lean: https://leanprover.github.io/

.. _`github.com/UniversalAlgebra/lean-ualib`: https://github.com/UniversalAlgebra/lean-ualib/

.. _lean-ualib: https://github.com/UniversalAlgebra/lean-ualib/

