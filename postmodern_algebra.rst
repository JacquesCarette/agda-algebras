.. File: postmodern_algebra.rst
.. Author: William DeMeo <williamdemeo@gmail.com>
.. Date: 14 May 2019
.. Updated: 5 Nov 2019
.. Updated: 11 Oct 2019
.. Copyright (c) 2019 William DeMeo (see the LICENSE file)

.. include:: _static/math_macros.rst

.. role:: cat
.. role:: code

.. _postmodern-algebra:

=======================
Postmodern Algebra [1]_
=======================

Up to now the goal of the :code:`ualib` development has been to remain faithful to the classical presentation of general (universal) algebra.  The motivation for this is so that the library seems natural to working algebraists.  However, there are real advantages to adopting a more modern and category theoretic approach.

In the remaining sections, we redesign the :code:`ualib` implementation to take advantage of the more elegant and more general language of category theory.  The downside is that the resulting definitions and theorem statements may turn out to be hardly recognizable to classical algebraists. 

----------------------------------------------------

.. index:: ! F-algebra, group, Set, Grp

.. _f-algebra:

F-algebras
----------

Let :math:`F` be an endofunctor on the category :cat:`Set`.

We define an **F-algebra** to be a structure :math:`𝔸 = ⟨A, f⟩`, where :math:`f : F A → A`.

Example: :cat:`Grp`
~~~~~~~~~~~~~~~~~~~

A **group** is an :math:`\FGrp`-algebra where :math:`\FGrp A = 1 + A + A × A`.

  A definition of a group that is closer to the standard one is the following:

  The *signature* of a group has three operation symbols, :math:`(e, \ ^{-1}, ∘)`.

   + :math:`e` is a nullary operation symbol (the "identity");
   + :math:`\ ^{-1}` is a unary operation symbol (the "inverse");
   + :math:`∘` is a binary operation symbol ("multiplication"). 

  Thus, a group is an algebraic structure, :math:`𝔸 = ⟨A, e, \ ^{-1}, ∘⟩`, where

   + :math:`e : A`;
   + :math:`^{-1} : A → A`;
   + :math:`∘ : A × A → A`.

  If we were to adopt Church's more precise :math:`λ` syntax, we could denote a group like this

  .. math:: 𝔸 = ⟨A, e, λ x . x^{-1}, λ x . λ y . x ∘ y⟩,

  and then the arity of each operation symbol could be read off immediately!

  To translate this into the language of F-algebras, observe that an element of the coproduct :math:`\FGrp A` has one of three forms,

   + :math:`ι_0 1 : 1`, the identity element of the group;
   + :math:`ι₁ x : A`, an arbitrary element of the group's universe;
   + :math:`ι₂ (x, y) : A × A`, an arbitrary pair of elements of the group's universe.

  So, we define and denote the group operations with a single symbol :math:`f : F A → A`, which acts on elements of the coproduct by pattern matching as follows:

   + :math:`f\ ι_0 1 = e`, the identity element of the group;
   + :math:`f\ ι₁ x = x^{-1}`, the group's inverse operation;
   + :math:`f\ ι₂ (x,y) = x\circ y`, the group's binary operation.

  In `Lean`_, the :code:`Grp` type could be implementation like this:

  .. code-block:: lean

     def f : 1 + ℕ + (ℕ × ℕ) → ℕ
     | ι₀ 1   := e
     | ι₁ x   := x⁻¹
     | ι₂ x y := x ∘ y

  .. code-block:: lean

      namespace hidden
      -- BEGIN
      variables {X Y Z : Type}
  
      def comp (f : Y → Z) (g : X → Y) : X → Z :=
      λx, f (g x)
  
      infixr  ` ∘ ` := comp
  
      def id (x : X) : X :=
      x
      -- END
      end hidden
  
.. index:: homomorphism
.. index:: ! group homomorphism
.. index:: ! F-algebra homomorphism

.. _f-algebra-homomorphism:

F-algebra homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~

Let :math:`𝔸 = ⟨A, f⟩` and :math:`𝔹 = ⟨B, g⟩` be two groups (i.e., :math:`\FGrp`-algebras).

A **homomorphism** from :math:`𝔸` to :math:`𝔹`, denoted by :math:`h : 𝔸 → 𝔹`, is a function :math:`h : A → B` that satisfies the following identity:

  .. math:: h ∘ f = g ∘ \FGrp h

To make sense of this identity, we must know how the functor :math:`\FGrp` acts on arrows (i.e., homomorphisms, like :math:`h`). It does so as follows:

  + :math:`(\mathrm F_{\mathbf{Grp}} h) (ι_0 1) = h(e)`;
  + :math:`(\mathrm F_{\mathbf{Grp}} h) (ι_1 x) = (h(x))^{-1}`;
  + :math:`(\mathrm F_{\mathbf{Grp}} h) (ι_2 (x,y)) = h(x) ∘ h(y)`.

Equivalently,

  + :math:`h ∘ f (ι_0 1) = h (e)` and :math:`g ∘ \FGrp h (ι_0 1) = g (h(e))`;
  + :math:`h \circ f (ι₁ x) = h (x^{-1})` and :math:`g ∘ \FGrp h (ι₁ x) = g (ι₁ h(x)) = (h(x))^{-1}`;
  + :math:`h \circ f (ι₂ (x,y)) = h (x ∘ y)` and :math:`g ∘ \FGrp h (ι₂ (x,y)) = g (ι₂ (h(x), h(y))) = h(x) ∘ h(y)`.

So, in this case, the indentity :math:`h ∘ f = g ∘ \FGrp h` reduces to

  + :math:`h (eᴬ) = g ( h(e) )`;
  + :math:`h (x^{-1_A}) = ( h(x) )^{-1_B}`;
  + :math:`h (x ∘ᴬ y) = h(x) ∘ᴮ h(y)`,

which are precisely the conditions we would normally verify when checking that :math:`h` is a group homomorphism.

--------------------

.. role:: cat
.. role:: code

.. _observations-categorically:

Observations, categorically
---------------------------

.. todo:: rewrite this section (it's still based on the classical treatment)

Let us revisit the list of observations we made (in classical notation) above in :numref:`Chapter %s <basic-facts>`.

Throught this section,

+ :math:`F` is an endofunctor on **Set**;
+ :math:`𝔸 = ⟨A, f^{𝔸}⟩, \ 𝔹 = ⟨B, f^{𝔹}⟩, \ ℂ = ⟨C, f^ℂ⟩\ ` are :ref:`F-algebras <f-algebra>`.

Suppose :math:`F` yields :math:`m` operation symbols and :math:`k_i` is the arity of the :math:`i`-th symbol:

.. math:: F A : ∐_{i=0}^{m-1}(\underline{k_i} → A) \quad \text{ and } \quad F B : ∐_{i=0}^{m-1}(\underline{k_i} → B).

Let :math:`g, h : \hom(𝔸, 𝔹)` be :ref:`F-algebra homomorphisms <f-algebra-homomorphism>` from 𝔸 to 𝔹:

  :math:`g, h : A → B` are set maps satisfying

  .. math:: g ∘ f^{𝔸} = f^{𝔹} ∘ F g \quad \text{ and } \quad h ∘ f^{𝔸} = f^{𝔹} ∘ F h.

.. index:: ! equalizer

The **equalizer** of :math:`g` and :math:`h` is the set

.. math:: E(g,h) = \{ a : A ∣ g(a) = h(a) \}.


.. _obs1cat:

.. proof:observation::

   :math:`E(g,h)` is a subuniverse of 𝔸.

   .. container:: toggle
 
      .. container:: header
 
         *Proof*
      
      Fix arbitrary :math:`0≤ i< m` and :math:`a : \underline{k_i} → E(g,h)`.

      We show that :math:`g (fᴬ (ι_i a)) = h (fᴬ (ι_i a))`, as this shows that :math:`E(g, h)` is closed under the i-th operation of :math:`⟨A, fᴬ⟩`.

      But this is trivial since, by definition of an :ref:`F-algebra homomorphism <f-algebra-homomorphism>`, we have

      .. math:: (g ∘ fᴬ)(ι_i a) = (fᴮ ∘ F g)(ι_i a) = (fᴮ ∘ F h)(ι_i a) = (h ∘ fᴬ)(ι_i a).
    
.. _obs2cat:

.. proof:observation::

   If the set :math:`X ⊆ A` generates 𝔸 and :math:`g|_X = h|_X`, then :math:`g = h`.

   .. container:: toggle
    
      .. container:: header
  
         *Proof*

      Suppose the subset :math:`X ⊆ A` generates :math:`⟨A, fᴬ⟩` and suppose :math:`g|_X = h|_X`.
 
      Fix an arbitrary :math:`a : A`. We show :math:`g(a) = h(a)`.
 
      Since :math:`X` generates 𝔸, there exists a term :math:`t` and a tuple :math:`x : ρt → X` of generators such that :math:`a = tᴬ x`.
 
      Therefore, since :math:`F g = F h` on :math:`X`, we have
    
      .. math:: g(a) = g(tᴬ x) = (tᴮ ∘ F g)(x) = (tᴮ ∘ F h)(x) = h(tᴬ x) = h(a).
    
.. _obs3cat:

.. proof:observation::

   If :math:`A, B` are finite and :math:`X` generates 𝔸, then :math:`|\hom(𝔸, 𝔹)| ≤ |B|^{|X|}`.

   .. container:: toggle
    
      .. container:: header
    
         *Proof*

      By :ref:`obs 2 <obs2cat>`, a homomorphism is uniquely determined by its restriction to a generating set.

      If :math:`X` generates 𝔸, then since there are exactly :math:`|B|^{|X|}` functions from :math:`X` to :math:`B` we have :math:`|\hom(𝔸, 𝔹)| ≤ |B|^{|X|}`.
    
.. _obs4cat:

.. proof:observation::

   If :math:`g : \epi (𝔸, 𝔹)` and :math:`h : \hom (𝔸, 𝐂)` satisfy :math:`\ker g ⊆ \ker h`, then

   .. math:: ∃ k ∈ \hom(𝔹, 𝐂)\ . \ h = k ∘ g.
    
   .. container:: toggle
    
      .. container:: header
    
         *Proof*

      We define :math:`k ∈ \hom(𝔹, 𝐂)` constructively, as follows:

      Fix :math:`b : B`.

      Since :math:`g` is surjective, the set :math:`g^{-1}\{b\} ⊆ A` is nonempty, and since :math:`\ker g ⊆ \ker h`, we see that every element of :math:`g^{-1}\{b\}` is mapped by :math:`h` to a single element of :math:`C`.

      Label this element :math:`c_b`. That is, :math:`h(a) = c_b`, for all :math:`a : g^{-1}\{b\}`.
   
      We define :math:`k(b) = c_b`. Since :math:`b` was arbitrary, :math:`k` is defined on all of :math:`B` in this way.
   
      Now it's easy to see that :math:`k g = h` by construction.
   
      Indeed, for each :math:`a ∈ A`, we have :math:`a ∈ g^{-1}\{g(a)\}`, so :math:`k(g(a)) = h(a)` by definition.
   
      To see that :math:`k` is a homomorphism, let there be :math:`m` operation symbols and let :math:`0≤ i< m` be arbitrary.
   
      Fix :math:`b : \underline{k_i} → B`.
   
      Since :math:`g` is surjective, for each :math:`i : \underline{k_i}`, the subset :math:`g^{-1}\{b(i)\}⊆ A` is nonempty and is mapped by :math:`h` to a single point of :math:`C` (since :math:`\ker g ⊆ \ker h`.
   
      Label this point :math:`c_i` and define :math:`c : \underline{k_i} → C` by :math:`c(i) = c_i`.
   
      We want to show :math:`(f^C ∘ F k) (b) = (k ∘ f^B)(b).`
   
      The left hand side is :math:`f^C c`, which is equal to :math:`(h ∘ fᴬ)(a)` for some :math:`a : \underline{k_i} → A`, since :math:`h` is a homomorphism.
   
      Therefore,
   
      .. math:: (f^C ∘ F k) (b) = (h ∘ f^A) (a) = (k ∘ g ∘ f^A)(a) = (k ∘ f^B ∘ F g)(a) = (k ∘ f^B)(b).
 
.. _obs5cat:

.. proof:observation::

   Let :math:`S = (F, ρ)` be a signature each :math:`f ∈ F` an :math:`(ρf)`-ary operation symbol.
 
   Define :math:`F_0 := \operatorname{Proj}(A)` and for all :math:`n > 0` in :math:`ω` let
 
   .. math:: F_{n+1} := F_n ∪ \{ f g ∣ f ∈ F, g : ρf → (F_n ∩ (ρg → A)) \}.
 
   Then :math:`\mathrm{Clo}^{𝔸}(F) = ⋃_n F_n`.
 
.. _obs6cat:

.. proof:observation::

   Let :math:`f` be a similarity type.
 
    (a) :math:`𝕋_ρ (X)` is generated by :math:`X`.
 
    (b) For every algebra :math:`𝔸 = ⟨A, F⟩` of type :math:`ρ` and every function :math:`h : X → A` there is a unique homomorphism :math:`g : 𝕋_ρ (X) → ⟨A, fᴬ⟩` such that :math:`g|_X = h`.
 
   .. container:: toggle
    
      .. container:: header
     
         *Proof*
     
      The definition of :math:`𝕋_ρ (X)` exactly parallels the construction in Theorem 1.14 :cite:`Bergman:2012`. That accounts for the first item.
     
      For b, define :math:`g(t)` by induction on :math:`|t|`.
     
      Suppose :math:`|t| = 0`.  Then :math:`t ∈ X ∪ \mathcal F_0`.
     
      If :math:`t ∈ X` then define :math:`g(t) = h(t)`. For :math:`t ∈ \mathcal F_0`, :math:`g(t) = t^{𝔸}`.
     
      Note that since :math:`𝔸 = ⟨A, fᴬ⟩` is an algebra of type :math:`f` and :math:`t` is a nullary operation symbol, :math:`t^{𝔸}` is defined.
     
      For the inductive step, let :math:`|t| = n + 1`. Then :math:`t = f(s_1, \dots, s_k)` for some :math:`f ∈ \mathcal F_k` and :math:`s_1, \dots, s_k` each of height at most :math:`n`. We define :math:`g(t) = f^{𝔸}(g(s_1), \dots, g(s_k))`.
     
      By its very definition, :math:`g` is a homomorphism. Finally, the uniqueness of :math:`g` follows from Exercise 1.16.6 in :cite:`Bergman:2012`.
 
.. _obs7cat:

.. proof:observation::

   Let :math:`𝔸 = ⟨A, f^{𝔸}⟩` and :math:`𝔹 = ⟨B, f^{𝔹}⟩` be algebras of type :math:`ρ`.
 
    (a) For every :math:`n`-ary term :math:`t` and homomorphism :math:`g : 𝔸 → 𝔹`, :math:`g(t^{𝔸}(a_1,\dots, a_n)) = t^{𝔹}(g(a_1),\dots, g(a_n))`.

    (b) For every term :math:`t ∈ T_ρ(X_ω)` and every :math:`θ ∈ \mathrm{Con}⟨A, fᴬ⟩`, :math:`𝔸 ≡_θ 𝔹` implies :math:`t^{𝔸}(𝔸) ≡_θ t^{𝔸}(𝔹)`.

    (c) For every subset :math:`Y` of :math:`A`,

        .. math:: \Sg^{𝔸}(Y) = \{ t^{𝔸}(a_1, \dots, a_n) : t ∈ Tᵨ (X_n), a_i ∈ Y, i ≤ n < ω\}.

   .. container:: toggle
    
      .. container:: header
    
        *Proof*
    
      The first statement is an easy induction on :math:`|t|`.
    
      The second statement follows from the first by taking :math:`⟨B, f^{𝔹}⟩ = ⟨A, f^{𝔸}⟩/θ` and :math:`g` the canonical homomorphism.
    
      For the third statement, again by induction on the height of :math:`t`, every subalgebra must be closed under the action of :math:`t^{𝔸}`.
    
      Thus the right-hand side is contained in the left. On the other hand, the right-hand side is clearly a subalgebra containing the elements of :math:`Y` (take :math:`t = x_1`) from which the reverse inclusion follows.

-----------------------------

.. rubric:: Footnotes

.. [1]
   The title of this chapter, "Postmodern Algebra," is borrowed from Johnathan Smith and Anna Romanowska, whose algebra textbook has the same title.

.. include:: hyperlink_references.rst

