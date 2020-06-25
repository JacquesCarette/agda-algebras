--FILE: UF-Truncation.agda
--DATE: 22 Apr 2020
--DATE: 15 May 2020
--BLAME: <williamdemeo@gmail.com>
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation
--      In particular, the quoted comments below, along with sections of code to which those
--      comments refer, are due to Martin Escardo. Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Truncation where

--open import Data.Product.Properties using (,-injectiveˡ;,-injectiveʳ;,-injective)

open import UF-Prelude using (Universe; 𝓣; 𝓤₀; 𝓤; 𝓥; 𝓦; _⁺; _̇;_⊔_; 𝓤ω; 𝑖𝑑; 𝟘; !𝟘; 𝟙; ⋆; 𝟙-induction; ¬; is-empty; _∘_; _,_; Σ; -Σ; pr₁; pr₂; Π; -Π; domain; codomain; _×_; _+_; inl; inr; Σ-induction; _≡_; refl; _∼_; transport; ap; _≡⟨_⟩_; _∎; _⁻¹; _⇔_; _iff_; ¬¬; rl-implication;lr-implication; 𝓤₁; id)

open import UF-Singleton using (is-set; is-singleton; is-subsingleton; singletons-are-subsingletons; center; is-center; EM; em-irrefutable; em'-irrefutable; is-prop; 𝟙-is-subsingleton; 𝟘-is-subsingleton)

open import UF-Equality using (wconstant; wconstant-endomap; has-section; singleton-types'-are-singletons; singleton-type'; _≃_;  id-≃; is-equiv; fiber; equiv-to-singleton; Σ-cong; transport-is-equiv; ≃-sym; invertibility-gives-≃; Eq→fun-is-equiv)

open import UF-Univalence using (to-subtype-≡; ×-is-subsingleton; subsingleton-criterion; equiv-to-subsingleton; logically-equivalent-subsingletons-are-equivalent; equiv-to-set; Id→fun; equivs-are-lc)

open import UF-Extensionality using (global-dfunext; global-hfunext; dfunext; Π-is-subsingleton; +-is-subsingleton'; hfunext-gives-dfunext; propext; being-equiv-is-subsingleton; Univalence; univalence-gives-global-dfunext; Ω; global-propext; _holds; Ω-ext; Ω-is-a-set; being-subsingleton-is-subsingleton; 𝓟; _∈_; ∈-is-subsingleton)

open import UF-Embedding using (is-embedding; being-embedding-is-subsingleton; Lift; Lift-≃; ≃-Lift; lift; univalence→')
open UF-Embedding.Lift using (lower)

--------------------------------------------------------------------------------------
--Subsingleton truncation
--Voevodsky's approach to subsingleton truncation.

--"The following is Voevosky's approach to saying that a type is inhabited in such a way that the statement
-- of inhabitation is a subsingleton, relying on function extensionality.
is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P

--"This says that if we have a function from `X` to a subsingleton `P`, then `P` must have a point. So this fails
-- when `X=𝟘`. Considering `P=𝟘`, we conclude that `¬¬ X` if `X` is inhabited, which says that `X` is non-empty.

--"For simplicity in formulation of the theorems, we assume *global* function extensionality. A type can be
-- pointed in many ways, but inhabited in at most one way:
inhabitation-is-subsingleton : global-dfunext
 → (X : 𝓤 ̇) → is-subsingleton (is-inhabited X)

inhabitation-is-subsingleton fe X =
  Π-is-subsingleton fe
    (λ P → Π-is-subsingleton fe
      (λ P✧ → Π-is-subsingleton fe
        (λ (f : X → P) → P✧)))

--"The following is the introduction rule for inhabitation, which says that pointed types are inhabited:
inhabited-intro : {X : 𝓤 ̇} → X → is-inhabited X
inhabited-intro x = λ P _ f → f x

--"And its recursion principle:
inhabited-recursion : {X P : 𝓤 ̇} → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-recursion P✧ f Xinhabited = Xinhabited (codomain f) P✧ f

--"And its computation rule:
inhabited-recursion-computation : {X P : 𝓤 ̇}
                (P✧ : is-subsingleton P)
                (f : X → P) (x : X)
             ----------------------------------------------------
 →           inhabited-recursion P✧ f (inhabited-intro x) ≡ f x

inhabited-recursion-computation P✧ f x = refl (f x)
--"So the point `x` inside `inhabited x` is available for use by any function `f` into a subsingleton,
-- via `inhabited-recursion`.

--"We can derive induction from recursion in this case, but its "computation rule" holds up to an
-- identification, rather than judgmentally:
inhabited-induction : global-dfunext
 →                    {X : 𝓤 ̇} {P : is-inhabited X → 𝓤 ̇}
                      (𝐼𝑆 : (X✶ : is-inhabited X) → is-subsingleton (P X✶))
                      (f : (x : X) → P (inhabited-intro x))
                      (X✶ : is-inhabited X) →  P X✶
inhabited-induction fe {X} {P} 𝐼𝑆 f X✶' = (X✶→PX✶) X✶'
 where
  X✶→PX✶ : is-inhabited X → P X✶'
  X✶→PX✶ = inhabited-recursion (𝐼𝑆 X✶') φ
    where
      φ : X → P X✶'
      φ x = transport P (inhabitation-is-subsingleton fe X (inhabited-intro x) X✶') (f x)

inhabited-computation : (fe : global-dfunext) {X : 𝓤 ̇} {P : is-inhabited X → 𝓤 ̇}
                        (𝐼𝑆 : (X✶ : is-inhabited X) → is-subsingleton (P X✶))
                        (f : (x : X) → P (inhabited-intro x)) (x : X)
                        -------------------------------------------------------
 →                      inhabited-induction fe 𝐼𝑆 f (inhabited-intro x)  ≡  f x
inhabited-computation fe 𝐼𝑆 f x = 𝐼𝑆 (inhabited-intro x) ( inhabited-induction fe 𝐼𝑆 f (inhabited-intro x) ) (f x)

--"The definition of inhabitation looks superficially like double negation. However, although we don't
-- necessarily have that `¬¬ P → P`, we do have that `is-inhabited P → P` if `P` is a subsingleton.
inhabited-subsingletons-are-pointed : (P : 𝓤 ̇)
 →          is-subsingleton P   →   is-inhabited P
           ----------------------------------------
 →                            P
inhabited-subsingletons-are-pointed P P✧ = inhabited-recursion P✧ (𝑖𝑑 P)

--"*Exercise*. [Show](https://lmcs.episciences.org/3217) that `is-inhabited X ⇔ ¬¬X` if and only if
-- excluded middle holds."
Sol1→ : global-dfunext → ({X : 𝓤 ̇} → (is-inhabited X ⇔ ¬¬ X))  →  EM 𝓤
Sol1→ {𝓤} dfe = →EM  --Recall, EM 𝓤 = (X : 𝓤 ̇) → is-subsingleton X → X + ¬ X
 where
  →EM : ({X : 𝓤 ̇} → is-inhabited X ⇔ ¬¬ X) → EM 𝓤
  →EM  impl X  X✧ = φ
    where
     em-irr : ¬¬( X + ¬ X)
     em-irr = em-irrefutable X X✧

     ζ : is-inhabited (X + ¬ X)
     ζ = rl-implication impl em-irr

     ξ : is-subsingleton (X + ¬ X)
     ξ = +-is-subsingleton' dfe {X} X✧

     φ : X + ¬ X
     φ = inhabited-subsingletons-are-pointed (X + ¬ X) ξ ζ

-- Sol1← : global-dfunext → EM 𝓤 → ({X : 𝓤 ̇} → (is-inhabited X ⇔ ¬¬ X))
-- Sol1← {𝓤} dfe = ?

inhabited-functorial : global-dfunext → (X : 𝓤 ⁺ ̇) (Y : 𝓤 ̇) → (X → Y) → is-inhabited X → is-inhabited Y
inhabited-functorial gfe X Y f = inhabited-recursion (inhabitation-is-subsingleton gfe Y) (inhabited-intro ∘ f)

--"This universe assignment for functoriality is fairly restrictive, but is the only possible one.
--"With this notion, we can define the image of a function as follows:
image' : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image' f = Σ y ꞉ codomain f , is-inhabited (Σ x ꞉ domain f , f x ≡ y)

{-"An attempt to define the image of `f` without the inhabitation predicate would be to take it to be
   `Σ y ꞉ codomain f , Σ x ꞉ domain f , f x ≡ y`. But we already know that this is equivalent to `X`.
   This is similar to what happens in set theory: the graph of any function is in bijection with its domain."
-}

--"We can define the restriction and corestriction of a function to its image as follows:
restriction' : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → image' f  →  Y
restriction'  f  ( y , _ ) = y

corestriction' : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → X  →  image' f
corestriction' f x = f x , inhabited-intro ( x , refl (f x) )

--"And we can define the notion of surjection as follows:
is-surjection' : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection' f = (y : codomain f) → is-inhabited (Σ x ꞉ domain f , f x ≡ y)

--"*Exercise*. The type `(y : codomain f) → Σ x ꞉ domain f , f x ≡ y`is equivalent to the type `has-section f`,
-- which is stronger than saying that `f` is a surjection.
-- Sol2 :  {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ((y : codomain f) → Σ x ꞉ domain f , f x ≡ y) ≡ (has-section f)
-- Sol2 f = {!!}

{-"There are two problems with this definition of inhabitation:
   1. Inhabitation has values in the next universe.
   2. We can eliminate into subsingletons of the same universe only.
   In particular, it is not possible to show that the map `X → is-inhabited X` is a surjection, or that
   `X → Y` gives `is-inhabited X → is-inhabited Y` for `X` and `Y` in arbitrary universes.

  "There are two proposed ways to solve this kind of problem:
   1. Voevodsky works with certain resizing rules for subsingletons. At the time of writing,
      the (relative) consistency of the system with such rules is an OPEN QUESTION.

   2. The HoTT book works with certain higher inductive types (HIT's), which are known to have models and hence
      to be (relatively) consistent. This is the same approach adopted by cubical type theory and cubical Agda. -}

-----------------------------------------------------------------------------------------------------------------
--An axiomatic approach.

--"A third possibility is to work with subsingleton truncations axiomatically
-- (see: https://lmcs.episciences.org/3217 ), which is compatible with the above two proposals.
-- We write this axiom as a record type rather than as an iterated `Σ` type for simplicity, where we use the
-- HoTT-book notation `∥ X ∥` for the inhabitation of `X`, called the propositional (or subsingleton) truncation
-- of `X`:
record subsingleton-truncations-exist : 𝓤ω where
 field
  ∥_∥                  : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-subsingleton   : {𝓤 : Universe} {X : 𝓤 ̇} → is-subsingleton ∥ X ∥
  ∣_∣                  : {𝓤 : Universe} {X : 𝓤 ̇} → X → ∥ X ∥
  ∥∥-recursion        : {𝓤 𝓥 : Universe} {X : 𝓤 ̇} {P : 𝓥 ̇} → is-subsingleton P → (X → P) → ∥ X ∥ → P

 infix 0 ∥_∥
--"This is the approach we adopt in our personal Agda development (see:  https://www.cs.bham.ac.uk/~mhe/agda-new/

--"We assume subsingleton truncations exist in the next few constructions, and we `open` the assumption to make
-- the above fields visible.
module basic-truncation-development (pt : subsingleton-truncations-exist) (hfe : global-hfunext) where

  open subsingleton-truncations-exist pt public

  hunapply : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g : Π A} → f ∼ g → f ≡ g
  hunapply = hfunext-gives-dfunext hfe

  ∥∥-recursion-computation : {X : 𝓤 ̇}{P : 𝓥 ̇}
                            (P✧ : is-subsingleton P)
                            (f : X → P)(x : X)
                          ------------------------------------
   →                        ∥∥-recursion P✧ f ∣ x ∣   ≡   f x
  ∥∥-recursion-computation P✧ f x = P✧ (∥∥-recursion P✧ f ∣ x ∣) (f x)

  ∥∥-induction : {X : 𝓤 ̇} {P : ∥ X ∥ → 𝓥 ̇}
   →            ((s : ∥ X ∥) → is-subsingleton (P s))
   →            ((x : X) → P ∣ x ∣)
   →            (s : ∥ X ∥) → P s
  ∥∥-induction {𝓤} {𝓥} {X} {P} Ps✧ f s = φ' s
   where
    φ : X → P s
    φ x = transport P (∥∥-is-subsingleton ∣ x ∣ s) (f x)
    φ' : ∥ X ∥  →   P s
    φ' = ∥∥-recursion ( Ps✧ s ) φ

  ∥∥-computation :  {X : 𝓤 ̇}{P : ∥ X ∥ → 𝓥 ̇}
                   (Ps✧ : (s : ∥ X ∥) → is-subsingleton (P s))
                   (f : (x : X) → P ∣ x ∣)   (x : X)
                  ------------------------------------------
   →               ∥∥-induction Ps✧ f ∣ x ∣   ≡   f x
  ∥∥-computation Ps✧ f x = Ps✧ ∣ x ∣ ( ∥∥-induction Ps✧ f ∣ x ∣ ) (f x)

  ∥∥-functor :  {X : 𝓤 ̇}{Y : 𝓥 ̇} → (X → Y)
               -----------------------------
   →                     ∥ X ∥ → ∥ Y ∥
  ∥∥-functor f = ∥∥-recursion ∥∥-is-subsingleton (λ x → ∣ f x ∣ )

  --"The subsingleton truncation of a type and its inhabitation are logically equivalent propositions:
  ∥∥-agrees-with-inhabitation : (X : 𝓤 ̇)
                        --------------------------
   →                     ∥ X ∥  ⇔  is-inhabited X
  ∥∥-agrees-with-inhabitation X = ∥X∥→Xinh , Xinh→∥X∥
   where
    ∥X∥→Xinh : ∥ X ∥ → is-inhabited X
    ∥X∥→Xinh = ∥∥-recursion (inhabitation-is-subsingleton hunapply X) inhabited-intro
    Xinh→∥X∥ : is-inhabited X → ∥ X ∥
    Xinh→∥X∥ = inhabited-recursion ∥∥-is-subsingleton ∣_∣

  --"Hence they differ only in size, and when size matters don't get in the way, we can use `is-inhabited`
  -- instead of `∥_∥` if we wish.

  ----------------------------
  -- Disjunction and existence.

  --"Disjunction and existence are defined as the truncation of `+` and `Σ`:
  _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ∨ B = ∥ A + B ∥
  infixl 20 _∨_

  ∃ : {X : 𝓤 ̇} → (X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
  ∃ A = ( ∥ Σ A ∥ )

  -∃ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
  -∃ X Y = ∃ Y
  syntax -∃ A (λ x → b) = ∃ x ꞉ A , b
  infixr -1 -∃

  ∨-is-subsingleton : {A : 𝓤 ̇} {B : 𝓥 ̇} → is-subsingleton (A ∨ B)
  ∨-is-subsingleton = ∥∥-is-subsingleton

  ∃-is-subsingleton : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → is-subsingleton (∃ A)
  ∃-is-subsingleton = ∥∥-is-subsingleton
  --See MHE's slides on univalent logic ( https://www.newton.ac.uk/seminar/20170711100011001 )
  --for further details.

  -- Images and surjections.
  image : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
  image f = Σ y ꞉ codomain f , ∃ x ꞉ domain f , f x ≡ y

  restriction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → image f → Y
  restriction f (y , _) = y

  corestriction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → X → image f
  corestriction f x = f x , ∣  ( x , refl (f x) ) ∣

  is-surjection : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
  is-surjection f = (y : codomain f) → ∃ x ꞉ domain f , f x ≡ y

  being-surjection-is-subsingleton : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
   →                                          is-subsingleton (is-surjection f)
  being-surjection-is-subsingleton f = Π-is-subsingleton hunapply (λ y → ∃-is-subsingleton)

  corestriction-surjection : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
   →                          is-surjection (corestriction f)
  corestriction-surjection f (y , s) = ∥∥-functor g s
   where
    g : (Σ x ꞉ domain f , f x ≡ y) → Σ x ꞉ domain f , corestriction f x ≡ (y , s)
    g (x , p) = x , to-subtype-≡ ( λ _ → ∃-is-subsingleton ) p

  surjection-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
   →                          is-surjection f   →   (P : Y → 𝓦 ̇)
   →                          ( (y : Y) →  is-subsingleton (P y) )
   →                          ( (x : X) →  P (f x) )
   →                          (y : Y)   →   P y

  surjection-induction f fsur P Py✧ Pf y = ∥∥-recursion (Py✧ y) φ (fsur y)
   where
    φ : fiber f y → P y              -- Σ (λ x → f x ≡ y) → P y
    φ ( x , fx≡y ) = transport P fx≡y (Pf x)

  --"*Exercise*. A map is an equivalence if and only if it is  both an embedding and a surjection.
  -- (To be solved shortly.)
  -- Sol3 : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-equiv f   ⇔  (is-embedding f) × (is-surjection f)
  -- Sol3 f = {!!} , {!!}

  --"This time we can prove that the map `x ↦ ∣ x ∣` of `X` into `∥ X ∥` is a surjection without the universe
  -- levels getting in our way:
  ∣∣-is-surjection : (X : 𝓤 ̇) → is-surjection (λ (x : X) → ∣ x ∣ )
  ∣∣-is-surjection X ✶ = γ
   where
    f : X → ∃ x ꞉ X , ∣ x ∣ ≡ ✶
    f x = ∣ ( x , ∥∥-is-subsingleton ∣ x ∣ ✶ ) ∣

    γ : ∃ x ꞉ X , ∣ x ∣ ≡ ✶
    γ = ∥∥-recursion ∥∥-is-subsingleton f ✶

  --"Saying that this surjection `X → ∥ X ∥` has a section for all `X` (we can pick a point of every inhabited type)
  -- amounts to global choice, which contradicts univalence, and also gives classical logic
  -- (see: https://homotopytypetheory.org/book/ and https://lmcs.episciences.org/3217 )

  --"The subsingleton truncation of a type is also known as its support and a type `X` is said to have split
  -- support if there is a *choice function* `∥ X ∥ → X`, which is automatically a section of the surjection
  -- `X → ∥ X ∥`.

  --"*Exercise.* Show that a type has split support if and only it is logically equivalent to a subsingleton.
  -- In particular, the type of invertibility data has split support, as it is logically equivalent to the
  -- equivalence property."

  --"*Exercise* (hard). If `X` and `Y` are types obtained by summing `x-` and `y`-many copies of the type
  -- `𝟙`, respectively, as in `𝟙 + 𝟙 + ... + 𝟙`, where `x` and `y` are natural numbers, then
  -- `∥ X ≡ Y ∥ ≃ (x ≡ y)` and the type `X ≡ X` has `x!` elements.

  --------------------------------------------------------------------------------------------------------
  -- A characterization of equivalences.
  --"Singletons are inhabited, of course:
  singletons-are-inhabited : (X : 𝓤 ̇) → is-singleton X → ∥ X ∥
  singletons-are-inhabited X X✦ = ∣ center X X✦ ∣

  --"And inhabited subsingletons are singletons:
  inhabited-subsingletons-are-singletons :
          (X : 𝓤 ̇)  →  ∥ X ∥  →  is-subsingleton X
         -------------------------------------------
   →                is-singleton X
  inhabited-subsingletons-are-singletons X t X✧ = ( c , X✧ c ) where
    c : X
    c = ∥∥-recursion X✧ (𝑖𝑑 X) t

  --"Hence a type is a singleton if and only if it is inhabited and a subsingleton:
  singleton-iff-inhabited-subsingleton : (X : 𝓤 ̇)
   →      is-singleton X  ⇔  (∥ X ∥ × is-subsingleton X)
  singleton-iff-inhabited-subsingleton X =
    ( λ (s : is-singleton X) → (singletons-are-inhabited X s , singletons-are-subsingletons X s) ) ,
          Σ-induction (inhabited-subsingletons-are-singletons X)

  -- (λ s → ∣ Σ.x s ∣ , singletons-are-subsingletons X s) , Σ-induction (inhabited-subsingletons-are-singletons X)

  --"By considering the unique map `X → 𝟙`, this can be regarded as a particular case of the fact that a map is
  -- an equivalence if and only if it is both an embedding and a surjection:
  equiv-iff-embedding-and-surjection : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
   →            is-equiv f   ⇔  (is-embedding f  ×  is-surjection f)
  equiv-iff-embedding-and-surjection f = ( eq→em×sur , eq←em×sur )
   where
    eq→em×sur : is-equiv f → is-embedding f × is-surjection f
    eq→em×sur feq = (λ y → singletons-are-subsingletons (fiber f y) (feq y)) ,
                    (λ y → singletons-are-inhabited (fiber f y) (feq y))

    eq←em×sur : is-embedding f × is-surjection f → is-equiv f
    eq←em×sur (fem , fsur) y = inhabited-subsingletons-are-singletons (fiber f y) (fsur y) (fem y)


  equiv-≡-embedding-and-surjection : {X : 𝓤 ̇}{Y : 𝓥 ̇}(f : X → Y) → propext (𝓤 ⊔ 𝓥)
   →                    is-equiv f  ≡  ( is-embedding f × is-surjection f )
  equiv-≡-embedding-and-surjection f pe = pe φ (×-is-subsingleton ζ ξ) α β
    where
     φ : is-prop (is-equiv f)
     φ = (being-equiv-is-subsingleton hunapply hunapply f)
     ζ : is-subsingleton (is-embedding f)
     ζ = being-embedding-is-subsingleton hunapply f
     ξ :  is-subsingleton (is-surjection f)
     ξ = being-surjection-is-subsingleton f
     α : is-equiv f → is-embedding f × is-surjection f
     α = lr-implication (equiv-iff-embedding-and-surjection f)
     β : is-embedding f × is-surjection f → is-equiv f
     β = rl-implication (equiv-iff-embedding-and-surjection f)

  ---------------------------------------------------------------------------------------------------
  -- Exiting subsingleton truncations.
  {-"We will see that global choice `(X : 𝓤 ̇) → ∥ X ∥ → X` is inconsistent with univalence, and also implies em.
     However, for some types `X`, we can prove that `∥ X ∥ → X`. We characterize such types as those that have
     `wconstant` endomaps (see: https://lmcs.episciences.org/3217/ )

    "Because, as we have seen, we have a logical equivalence `∥ X ∥ ⇔ is-inhabited X`, it suffices to discuss
     `is-inhabited X → X`, which can be done in our spartan MLTT without any axioms for univalent mathematics
     (and hence also with axioms for univalent mathematics, including non-constructive ones such as em and choice)

    "For any type `X`, we have `is-inhabited X → X` iff `X` has a designated wconstant endomap. To prove this we
     first show that the type of fixed points of a `wconstant` endomap is a subsingleton. -}

  --"We first define the type of fixed points:
  fix : {X : 𝓤 ̇} → (X → X) → 𝓤 ̇
  fix f = Σ x ꞉ domain f , f x ≡ x

  --"Of course any fixed point of `f` gives an element of `X`:
  from-fix : {X : 𝓤 ̇} (f : X → X) → fix f → X
  from-fix f = pr₁

  --"Conversely, if f is wconstant then ∀ x we have that f x is a fixpoint of f, and hence from any element of
  -- X we get a fixpoint of f:
  to-fix : {X : 𝓤 ̇} (f : X → X) → wconstant f → X → fix f
  to-fix f κ x = f x , κ (f x) x

  --"The following is trivial if the type `X` is a set. What may be surprising is that it holds for arbitrary
  -- types, because in this case the identity type `f x ≡ x` is in general not a subsingleton.
  fix-is-subsingleton : {X : 𝓤 ̇} (f : X → X) → wconstant f → is-subsingleton (fix f)
  fix-is-subsingleton {𝓤} {X} f κ = γ
   where
    a : (y x : X) → (f x ≡ x) ≃ (f y ≡ x)
    a y x = transport (_≡ x) (κ x y) , transport-is-equiv (_≡ x) (κ x y)

    b : (y : X) → fix f ≃ singleton-type' (f y)
    b y = Σ-cong (a y)

    c : (y : X) → is-singleton (fix f)
    c y = equiv-to-singleton (b y) (singleton-types'-are-singletons X (f y))

    d : fix f → is-singleton (fix f)
    d = c ∘ from-fix f

    γ : is-subsingleton (fix f)
    γ = subsingleton-criterion d

  --"*Exercise.* Formulate and prove the fact that the type `fix f` has the universal property of the subsingleton
  -- truncation of `X` if `f` is `wconstant`. Moreover, argue that the computation rule for recursion holds
  -- definitionally in this case. This is an example of a situation where the truncation of a type just is
  -- available in MLTT without axioms or extensions.

  --"We use `fix-is-subsingleton` to show that the type `is-inhabited X → X` is logically equivalent to the
  -- type `wconstant-endomap X`, where one direction uses function extensionality. We refer to a function
  -- `is-inhabited X → X` as a *choice function* for `X`. So the claim is that
  --
  --       A TYPE HAS A CHOICE FUNCTION IFF IT HAS A DESIGNATED `wconstant` ENDOMAP.
  --
  choice-function : 𝓤 ̇ → 𝓤 ⁺ ̇
  choice-function X = is-inhabited X → X

  --"With a constant endomap of `X`, we can exit the truncation `is-inhabited X` in pure MLTT:
  wconstant-endomap-gives-choice-function : {X : 𝓤 ̇} → wconstant-endomap X → choice-function X
  wconstant-endomap-gives-choice-function {𝓤} {X} (f , κ) = from-fix f ∘ γ
   where
    γ : is-inhabited X → fix f
    γ = inhabited-recursion (fix-is-subsingleton f κ) (to-fix f κ)

  --"For the converse we use function extensionality (to know that the type `is-inhabited X` is a subsingleton
  -- in the construction of the `wconstant` endomap):
  choice-function-gives-wconstant-endomap : global-dfunext
   →          {X : 𝓤 ̇}  →  choice-function X  →  wconstant-endomap X
  choice-function-gives-wconstant-endomap fe {X} cf = f , κ
   where
    f : X → X
    f = cf ∘ inhabited-intro
    κ : wconstant f
    κ x y = ap cf (inhabitation-is-subsingleton fe X (inhabited-intro x) (inhabited-intro y) )

  --[SKIPPING the following example for now  !!! maybe come back later !!!]
  --"As an application, we show that if the type of roots of a function `f : ℕ → ℕ` is inhabited, then it is
  -- pointed. In other words, with the information that there is some root, we can find an explicit root.
  --\begin{code}\end{code}

  --"Given a root, we find a minimal root (below it, of course) by bounded search, and this gives a constant
  -- endomap of the type of roots:
  --\begin{code}\end{code}

  --"The crucial property of the function `μρ f` is that it is `wconstant`:
  --\begin{code}\end{code}

  --"Using the `wconstancy` of `μρ f`, if a root of `f` exists, then we can find one (which in fact will be the
  -- minimal one):
  --\begin{code}\end{code}

  --"In the following example, we first hide a root with `inhabited-intro` and then find the minimal root with
  -- search bounded by this hidden root:
  --\begin{code}\end{code}

  --"We hide the root `8` of `f`:
  --\begin{code}\end{code}

  --"We have that `x` evaluates to `2`, which is clearly the minimal root of `f`:
  --\begin{code}\end{code}

  --"Thus, even though the type `is-inhabited A` is a subsingleton for any type `A`, the function
  -- `inhabited-intro : A → is-inhabited A` doesn't
  -- erase information. We used the information contained in `root-existence` as a bound for searching for the
  -- minimal root.

  --"Notice that this construction is in pure (spartan) MLTT without assumptions. Now we repeat part of the
  -- above using the existence of small truncations and functional extensionality as assumptions, replacing
  -- `is-inhabited` by `∥_∥`:
  --\begin{code}\end{code}

  --"This time, because the existence of propositional truncations is an assumption for this submodule, we don't
  -- have that `x` evaluates to `2`, because the computation rule for truncation doesn't hold definitionally.
  -- But we do have that `x` is `2`, applying the computation rule manually.
  --\begin{code}\end{code}

  --"In CUBICAL AGDA, with the truncation defined as a higher inductive type, `x` would compute to `2`
  -- automatically, like in our previous example using Voevodsky's truncation `is-inhabited`.

  --"This concludes the example."

  --"We also have:
  wconstant-endomap-gives-∥∥-choice-function : {X : 𝓤 ̇} → wconstant-endomap X → ( ∥ X ∥ → X )
  wconstant-endomap-gives-∥∥-choice-function {𝓤}{X} (f , κ) = from-fix f ∘ γ
   where
    γ : ∥ X ∥ → fix f
    γ = ∥∥-recursion (fix-is-subsingleton f κ) (to-fix f κ)

  ∥∥-choice-function-gives-wconstant-endomap : {X : 𝓤 ̇} → ( ∥ X ∥ → X ) → wconstant-endomap X
  ∥∥-choice-function-gives-wconstant-endomap {𝓤} {X} cf = f , κ
   where
    f : X → X
    f = cf ∘ ∣_∣

    κ : wconstant f
    κ x y = ap cf (∥∥-is-subsingleton ∣ x ∣ ∣ y ∣)

  --"There is another situation in which we can eliminate truncations that is often useful in practice.
  -- The universal property of subsingleton truncation says that we can get a function `∥ X ∥ → Y` provided
  -- the type `Y` is a subsingleton and we have a given function `X → Y`. Because `Y` is a subsingleton,
  -- the given function is automatically `wconstant`. Hence the following generalizes this to the situation
  -- in which `Y` is a set:
  ∥∥-recursion-set : (X : 𝓤 ̇) (Y : 𝓥 ̇) → is-set Y → (f : X → Y) → wconstant f → ∥ X ∥ → Y
  ∥∥-recursion-set {𝓤}{𝓥} X Y Yset f κ = f'
   where
    ψ : (y y' : Y) → (Σ x ꞉ X , f x ≡ y) → (Σ x' ꞉ X , f x' ≡ y') → y ≡ y'
    ψ y y' (x , fx≡y) (x' , fx'≡y') =  y       ≡⟨ ( fx≡y )⁻¹ ⟩
                                              f x     ≡⟨ κ x x' ⟩
                                              f x'    ≡⟨ fx'≡y' ⟩
                                              y'      ∎


    φ : (y y' : Y) → (∃ x ꞉ X , f x ≡ y) → (∃ x' ꞉ X , f x' ≡ y') → y ≡ y'
    φ y y' u u' = ∥∥-recursion (Yset y y') (λ - → ∥∥-recursion (Yset y y') (ψ y y' -) u') u

    P : 𝓤 ⊔ 𝓥 ̇
    P = image f

    P✧ : is-subsingleton P
    P✧ (y , u) (y' , u') = to-subtype-≡ (λ _ → ∃-is-subsingleton) (φ y y' u u')

    g : ∥ X ∥ → P
    g = ∥∥-recursion P✧ (corestriction f)

    h : P → Y
    h = restriction f

    f' : ∥ X ∥ → Y
    f' = h ∘ g

  --"If we try to do this with Voevodsky's truncation `is-inhabited`, we stumble into an insurmountable
  -- problem of size."


----------------------------------------------------------------------------------------------------

--FILE: Resizing.agda
--DATE: 17 Apr 2020
--BLAME: <williamdemeo@gmail.com>
--REF: Based on Martin Escardo's course notes
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#resizing


--------------------------------------------------------------------------------------
-- Propositional resizing, truncation and the powerset

{-"Voevodsky considered resizing rules for a type theory for univalent foundations.
   ( see: https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf )
   These rules govern the syntax of the formal system, and hence are of a meta-mathematical nature.

   Here we instead formulate, in our type theory without such rules, mathematical resizing principles.
   These principles are provable in the system with Voevodsky's rules.

   The consistency of the resizing *rules* is an open problem at the time of writing, but the resizing
   *principles* are consistent relative to ZFC with Grothendieck universes, because they follow from
   excluded middle, which is known to be validated by the simplicial-set model.

   It is also an open problem whether the resizing principles discussed below have a computational interpretation.
-}

-----------------------
--Propositional resizing.
--"We say that a type `X` has size `𝓥` if it is equivalent to a type in the universe `𝓥`:
_has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
X has-size 𝓥 = Σ Y ꞉ 𝓥 ̇ , X ≃ Y

--"The propositional resizing principle from a universe `𝓤` to a universe `𝓥` says that every subsingleton
-- in `𝓤` has size `𝓥`:
propositional-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
propositional-resizing 𝓤 𝓥 = (P : 𝓤 ̇) → is-subsingleton P → P has-size 𝓥

--"Propositional resizing from a universe to a higher universe just holds, of course:
resize-up : (X : 𝓤 ̇) → X has-size (𝓤 ⊔ 𝓥)
resize-up {𝓤} {𝓥} X = ( Lift 𝓥 X , ≃-Lift X )

resize-up-subsingleton : propositional-resizing 𝓤 (𝓤 ⊔ 𝓥)
resize-up-subsingleton {𝓤} {𝓥} P P✧ = resize-up {𝓤} {𝓥} P

--"We use the following to work with propositional resizing more abstractly:
resize : propositional-resizing 𝓤 𝓥 → (P : 𝓤 ̇) (P✧ : is-subsingleton P) → 𝓥 ̇
resize ρ P P✧ = pr₁ (ρ P P✧) --[Retrieve Y : 𝓥 ̇  ( where X : 𝓤 ̇ and X ≃ Y ).]

resize-is-subsingleton : (ρ : propositional-resizing 𝓤 𝓥)
                         (P : 𝓤 ̇) (P✧ : is-subsingleton P)
 →                       is-subsingleton (resize ρ P P✧)
resize-is-subsingleton ρ P P✧ = equiv-to-subsingleton γ P✧
 where
  γ : resize ρ P P✧ ≃ P
  γ = ≃-sym (pr₂ (ρ P P✧))

to-resize : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇) (P✧ : is-subsingleton P)
 →          P → resize ρ P P✧
to-resize ρ P P✧ = let PR✧ = pr₂ (ρ P P✧) in pr₁ PR✧

from-resize : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇) (P✧ : is-subsingleton P)
 →            resize ρ P P✧ → P
from-resize ρ P P✧ = let PR✧ = pr₂ (ρ P P✧) in pr₁ (≃-sym PR✧)

Propositional-resizing : 𝓤ω
Propositional-resizing = { 𝓤 𝓥 : Universe } → propositional-resizing 𝓤 𝓥

-----------------------------------------------
--Excluded middle gives propositional resizing.

--"Propositional resizing is consistent, because it is implied by excluded middle, which is consistent
-- (with or without univalence):
EM-gives-PR : EM 𝓤 → propositional-resizing 𝓤 𝓥
EM-gives-PR {𝓤} {𝓥} em P P✧ = Q (em P P✧) , γ
 where
  Q : P + ¬ P → 𝓥 ̇
  Q (inl _) = Lift 𝓥 𝟙
  Q (inr _) = Lift 𝓥 𝟘

  Qd✧ : (d : P + ¬ P) → is-subsingleton (Q d)
  Qd✧ (inl _) = equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton
  Qd✧ (inr _) = equiv-to-subsingleton (Lift-≃ 𝟘) 𝟘-is-subsingleton

  f : (d : P + ¬ P) → P → Q d
  f (inl p) p' = lift ⋆
  f (inr ¬p) p = !𝟘 (Lift 𝓥 𝟘) (¬p p)   -- lift (¬p p)

  g : (d : P + ¬ P) → Q d → P
  g (inl p) q = p
  g (inr ¬p) q = !𝟘 P (lower q)

  γ : P ≃ Q (em P P✧)
  γ = logically-equivalent-subsingletons-are-equivalent
          P ( Q (em P P✧) ) P✧ ( Qd✧ (em P P✧) ) ( f (em P P✧) , g (em P P✧) )


------------------------------------------------------
--The propositional resizing axiom is a subsingleton

--"To show that the propositional resizing principle is a subsingleton, we use univalence here.
has-size-is-subsingleton : Univalence → (X : 𝓤 ̇) (𝓥 : Universe) → is-subsingleton (X has-size 𝓥)
has-size-is-subsingleton {𝓤} 𝓤★ X 𝓥 = univalence→' (𝓤★ 𝓥) (𝓤★ (𝓤 ⊔ 𝓥) ) X

PR-is-subsingleton : Univalence → is-subsingleton (propositional-resizing 𝓤 𝓥)
PR-is-subsingleton {𝓤} {𝓥} 𝓤★ = Π-is-subsingleton α β
 where
  α : dfunext (𝓤 ⁺) (𝓤 ⊔ (𝓥 ⁺)) -- f ∼ g → f ≡ g
  α  = univalence-gives-global-dfunext 𝓤★
  β : (X : 𝓤 ̇) → is-subsingleton (is-subsingleton X → X has-size 𝓥)
  β = λ P → Π-is-subsingleton (univalence-gives-global-dfunext 𝓤★)
           λ _ → has-size-is-subsingleton 𝓤★ P 𝓥

--"*Exercise*. It is possible to show that the propositional resizing principle is a subsingleton using
-- propositional and functional extensionality instead of univalence.
-- (see: https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Size.html )

-- SOLUTION.
-- extensionality-gives-PR-is-subsingleton : global-propext → global-dfunext
--  →                                        (P : 𝓤 ̇) → is-subsingleton P
--  →                                        (𝓥 : Universe)
--                                           ---------------------------------
--  →                                        is-subsingleton ( P has-size 𝓥)
-- extensionality-gives-PR-is-subsingleton {𝓤} pe fe P P✧ 𝓥 = equiv-to-subsingleton {!!} {!!}

------------------------------
--Propositional impredicativity
--see: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#prop-impred

--"We consider two notions of propositional impredicativity:
Impredicativity : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Impredicativity 𝓤 𝓥 = (Ω 𝓤) has-size 𝓥

is-impredicative : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-impredicative 𝓤 = Impredicativity 𝓤 𝓤

PR-gives-Impredicativity⁺ : global-propext → global-dfunext
 →                          propositional-resizing 𝓥 𝓤
 →                          propositional-resizing 𝓤 𝓥
                           ----------------------------------
 →                          Impredicativity 𝓤 (𝓥 ⁺)
PR-gives-Impredicativity⁺ {𝓥}{𝓤} pe fe ρ σ = γ
  where
    -- Recall, `Ω 𝓤 = Σ P ꞉ 𝓤 ̇ , is-subsingleton P`
    ψ : Ω 𝓤 → Ω 𝓥
    ψ (P , P✧) = resize σ P P✧ , resize-is-subsingleton σ P P✧
    φ  : Ω 𝓥 → Ω 𝓤
    φ (Q , Q✧) = resize ρ Q Q✧ , resize-is-subsingleton ρ Q Q✧
    φ∼ψ : (p : Ω 𝓤) → φ (ψ p) ≡ p
    φ∼ψ (P , P✧) = Ω-ext fe pe a b
     where
      Q : 𝓥 ̇
      Q = resize σ P P✧

      Q✧ : is-subsingleton Q
      Q✧ = resize-is-subsingleton σ P P✧

      a : φ (ψ (P , P✧)) holds → (P , P✧) holds
      a = from-resize σ P P✧ ∘ from-resize ρ Q Q✧

      b :  P → resize ρ Q Q✧
      b = to-resize ρ Q Q✧ ∘ to-resize σ P P✧

    ψ∼φ : (q : Ω 𝓥) → ψ (φ q) ≡ q
    ψ∼φ (Q , Q✧) = Ω-ext fe pe a b
     where
      P : 𝓤 ̇
      P = resize ρ Q Q✧

      P✧ : is-subsingleton P
      P✧ = resize-is-subsingleton ρ Q Q✧

      a : resize σ P P✧ → Q
      a = from-resize ρ Q Q✧ ∘ from-resize σ P P✧

      b :  Q → resize σ P P✧
      b = to-resize σ P P✧ ∘ to-resize ρ Q Q✧

    γ : (Ω 𝓤) has-size (𝓥 ⁺)
    γ = Ω 𝓥 , invertibility-gives-≃ ψ (φ , φ∼ψ , ψ∼φ)

--"Propositional resizing doesn't imply that the first universe 𝓤₀ is propositionally impredicative, but it
-- does imply that all other, successor, universes 𝓤 ⁺ are.
PR-gives-impredicativity⁺ :  global-propext → global-dfunext
 →                           propositional-resizing (𝓤 ⁺) 𝓤
                             -------------------------------
 →                            is-impredicative (𝓤 ⁺)

PR-gives-impredicativity⁺ pe fe = PR-gives-Impredicativity⁺ pe fe λ P _ → resize-up P

--"What we get with propositional resizing is that all types of subsingletons of any universe 𝓤 are equivalent to Ω 𝓤₀, which
-- lives in the second universe 𝓤₁:
PR-gives-impredicativity₁ : global-propext → global-dfunext
 →                          propositional-resizing 𝓤 𝓤₀
                            -------------------------------
 →                           Impredicativity 𝓤 𝓤₁

PR-gives-impredicativity₁ pe fe = PR-gives-Impredicativity⁺ pe fe (λ P _ → resize-up P)

--"*Exercise*. Excluded middle gives the impredicativity of the first universe, and of all other universes."
-- (see: https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Size.html )

-- SOLUTION.  Recall, `EM 𝓤 X` says: if X is a subsingleton, then either X or ¬ X.
-- More, precisely, `EM 𝓤 = (X : 𝓤 ̇) → is-subsingleton X → X + ¬ X`
-- EM-gives-impredicativity₀ : global-propext → global-dfunext → EM 𝓤
--  →                          is-impredicative 𝓤₀
-- EM-gives-impredicativity₀ gpe gdfe em = {!!}

-- EM-gives-impredicativity : global-propext → global-dfunext → EM 𝓤
--  →                         (𝓥 : Universe) → is-impredicative 𝓥
-- EM-gives-impredicativity gpe gdfe em 𝓥 = {!!}

--We could ask more generally whether the following holds:
-- EM-gives-Impredicativity : global-propext → global-dfunext → EM 𝓤 → (𝓥 : Universe) → Impredicativity 𝓤₀ 𝓥
-- EM-gives-Impredicativity gpe gdfe em 𝓥 = {!!}

--"We also have that moving `Ω` around universes moves subsingletons around universes:
Impredicativity-gives-PR : propext 𝓤 → dfunext 𝓤 𝓤 → Impredicativity 𝓤 𝓥
 →                         propositional-resizing 𝓤 𝓥

Impredicativity-gives-PR {𝓤} {𝓥} pe fe ( 𝓞 , Ω𝓤≃𝓞 ) P P✧ = Q , P≃Q
 where
  𝟙' : 𝓤 ̇
  𝟙' = Lift 𝓤 𝟙
  𝟙'✧ : is-subsingleton 𝟙'
  𝟙'✧ (lift ⋆) (lift ⋆) = refl (lift ⋆)
  down : Ω 𝓤 → 𝓞
  down = pr₁ Ω𝓤≃𝓞
  𝓞-is-set : is-set 𝓞
  𝓞-is-set = equiv-to-set (≃-sym Ω𝓤≃𝓞 ) (Ω-is-a-set fe pe)
  Q : 𝓥 ̇
  Q = down (𝟙' , 𝟙'✧) ≡ down (P , P✧)
  Q✧ : is-subsingleton Q
  Q✧ = 𝓞-is-set (down (Lift 𝓤 𝟙 , 𝟙'✧) ) (down (P , P✧))
  φ : Q → P
  φ q = Id→fun (ap _holds (equivs-are-lc down (Eq→fun-is-equiv Ω𝓤≃𝓞) q) ) (lift ⋆)
  γ : P → Q
  γ p = ap down (to-subtype-≡ (λ _ → being-subsingleton-is-subsingleton fe)
                                   (pe 𝟙'✧ P✧ (λ _ → p) (λ _ → lift ⋆ ) ) )
  P≃Q : P ≃ Q
  P≃Q = logically-equivalent-subsingletons-are-equivalent P Q P✧ Q✧ (γ , φ)

--"*Exercise*. `propext` and `funext` and excluded middle together imply that `Ω 𝓤` has size `𝓤₀`.
-- (see: https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Size.html )
--
-- SOLUTION. (see: https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Size.html#8181 )
-- Ω-global-resizing-from-em-pe-fe : EM 𝓤 → propext 𝓤 → funext 𝓤 𝓤
--  →                                (𝓥 : Universe) → (Ω 𝓤) has-size 𝓥
-- Ω-global-resizing-from-em-pe-fe {𝓤} lem pe fe 𝓥 = {!𝟙 {𝓥} + 𝟙 {𝓤} , invertibility-gives-≃ φ ?!}

-------------------------------------------------------------
--Propositional resizing gives subsingleton truncation

--"Using Voevodsky's [truncation] construction and propositional resizing, we get that function extensionality
-- implies that subsingleton truncations exist:
PR-gives-existence-of-truncations : global-dfunext
 →                Propositional-resizing →  subsingleton-truncations-exist

PR-gives-existence-of-truncations fe R =
 record
 {
   ∥_∥ = λ {𝓤} X → resize R (is-inhabited X) (inhabitation-is-subsingleton fe X) ;
   ∥∥-is-subsingleton = λ {𝓤} {X} → resize-is-subsingleton R (is-inhabited X) (inhabitation-is-subsingleton fe X) ;
   ∣_∣ = λ {𝓤}{X} x → to-resize R (is-inhabited X) (inhabitation-is-subsingleton fe X) (inhabited-intro x) ;
   ∥∥-recursion = λ {𝓤} {𝓥} {X}{P} i u s → from-resize R P i (inhabited-recursion (resize-is-subsingleton R P i)
        (to-resize R P i ∘ u) (from-resize R (is-inhabited X) (inhabitation-is-subsingleton fe X) s) )
 }

------------------------------------------------------
--The powerset in the presence of propositional resizing

--"As a second, important, use of resizing, we revisit the powerset. First, given a set of subsets, that is,
-- an element of the double powerset, we would like to consider its union. We investigate its existence in a
-- submodule with assumptions.
module powerset-union-existence (pt : subsingleton-truncations-exist) (hfe : global-hfunext) where

  open basic-truncation-development pt hfe

  --"Unions of *families* of subsets exist under the above assumption of truncation existence, provided the index
  -- set `I` is in a universe equal or below the universe of the type `X` of which we are taking the powerset:
  family-union : {X : 𝓤 ⊔ 𝓥 ̇} {I : 𝓥 ̇} → ( I → 𝓟 X ) → 𝓟 X
  family-union {𝓤} {𝓥} {X} {I} A = λ x → ( ∃ i ꞉ I , x ∈ A i ) , ∃-is-subsingleton

  --"Notice the increase of universe levels in the iteration of powersets:
  𝓟𝓟 : 𝓤 ̇ → 𝓤 ⁺ ⁺ ̇
  𝓟𝓟 X = 𝓟 ( 𝓟 X )

  --"The following doesn't assert that unions of collections of subsets are available.
  -- It says what it means for them to be available:
  existence-of-unions : (𝓤 : Universe) → 𝓤 ⁺ ⁺ ̇
  existence-of-unions 𝓤 = (X : 𝓤 ̇) (𝓐 : 𝓟𝓟 X) → Σ B ꞉ 𝓟 X , ( (x : X) → ( (x ∈ B) ⇔ ( ∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A) ) ) )

  --"One may wonder whether there are different universe assignments for the above definition, for instance
  -- whether we can instead assume `𝓐 : (X → Ω 𝓥) → Ω 𝓦` for suitable universes `𝓥` and `𝓦`, possibly
  -- depending on `𝓤`. That this is not the case can be checked by writing the above definition in the
  -- following alternative form:
  existence-of-unions₁ : (𝓤 : Universe) → _ ̇
  existence-of-unions₁ 𝓤 = (X : 𝓤 ̇) (𝓐 : (X → Ω _) → Ω _)
   →      Σ B ꞉ (X → Ω _) ,  ( (x : X) →   ( (x ∈ B)  ⇔  ( ∃ A ꞉ (X → Ω _ ) , (A ∈ 𝓐) × (x ∈ A) ) ) )

  --"The fact that Agda accepts the above definition without errors means that there is a unique way to fill
  -- each `_`, which has to be the following.
  existence-of-unions₂ : (𝓤 : Universe) → 𝓤 ⁺ ⁺ ̇
  existence-of-unions₂ 𝓤 = (X : 𝓤 ̇) ( 𝓐 : (X → Ω 𝓤) → Ω (𝓤 ⁺) )
   →      Σ B ꞉ (X → Ω 𝓤) ,  ( (x : X) →   ( (x ∈ B)  ⇔  ( ∃ A ꞉ (X → Ω 𝓤 ) , (A ∈ 𝓐) × (x ∈ A) ) ) )

  existence-of-unions-agreement : existence-of-unions 𝓤 ≡ existence-of-unions₂ 𝓤
  existence-of-unions-agreement = refl _

  --"*Exercise*. Show that the existence of unions is a subsingleton type."
  -- SOLUTION.
  -- existence-of-unions-is-subsingleton : (𝓤 : Universe) → is-subsingleton (existence-of-unions 𝓤)
  -- existence-of-unions-is-subsingleton 𝓤 = {!!}

  --"Without propositional resizing principles, it is not possible to establish the existence.
  existence-of-unions-gives-PR : existence-of-unions 𝓤
   →                             propositional-resizing (𝓤 ⁺) 𝓤
  existence-of-unions-gives-PR {𝓤} α = γ
    where
      γ : (P : 𝓤 ⁺ ̇ ) → is-subsingleton P → P has-size 𝓤
      γ P P✧ = Q , e
        where
          𝟙ᵤ : 𝓤 ̇
          𝟙ᵤ = Lift 𝓤 𝟙
          ⋆ᵤ : 𝟙ᵤ
          ⋆ᵤ = lift ⋆
          𝟙ᵤ-is-subsingleton : is-subsingleton 𝟙ᵤ
          𝟙ᵤ-is-subsingleton = equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton
          𝓐 : 𝓟𝓟 𝟙ᵤ
          𝓐 = λ (A : 𝓟 𝟙ᵤ) → P , P✧
          B : 𝓟 𝟙ᵤ
          B = pr₁ (α 𝟙ᵤ 𝓐)
          φ : (x : 𝟙ᵤ) → (x ∈ B) ⇔ (∃ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (x ∈ A) )
          φ = pr₂ (α 𝟙ᵤ 𝓐)
          Q : 𝓤 ̇
          Q = ⋆ᵤ ∈ B
          Q✧ : is-subsingleton Q
          Q✧ = ∈-is-subsingleton B ⋆ᵤ
          f : P → Q
          f p = b
            where
              a : Σ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (⋆ᵤ ∈ A)
              a = (λ (x : 𝟙ᵤ) → 𝟙ᵤ , 𝟙ᵤ-is-subsingleton) , p , ⋆ᵤ
              b : ⋆ᵤ ∈ B
              b = rl-implication (φ ⋆ᵤ) ∣ a ∣
          g : Q → P
          g q = ∥∥-recursion P✧ b a
            where
              a : ∃ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (⋆ᵤ ∈ A)
              a = lr-implication (φ ⋆ᵤ) q
              b : (Σ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (⋆ᵤ ∈ A) ) → P
              b (A , m , _) = m
          e : P ≃ Q
          e = logically-equivalent-subsingletons-are-equivalent P Q P✧ Q✧ (f , g)

  --"The converse also holds, with an easier construction:
  PR-gives-existence-of-unions : propositional-resizing (𝓤 ⁺) 𝓤
   →                             existence-of-unions 𝓤
  PR-gives-existence-of-unions {𝓤} ρ X 𝓐 = 𝓟X , α
   where
    β : X → 𝓤 ⁺ ̇
    β x = ∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A)

    βx✧ : (x : X) → is-subsingleton (β x)
    βx✧ x = ∃-is-subsingleton

    𝓟X : 𝓟 X
    𝓟X x = (resize ρ (β x) (βx✧ x) , resize-is-subsingleton ρ (β x) (βx✧ x) )

    α : (x : X) →(𝓟X x holds) ⇔ -∃ (𝓟 X) (λ A → (𝓐 A holds) × (A x holds))
    α x = from-resize ρ (β x) (βx✧ x) , to-resize ρ (β x) (βx✧ x)


--"We now close the above submodule and start another one with different assumptions:
module basic-powerset-development (hfe : global-hfunext) (ρ : Propositional-resizing) where
  pt : subsingleton-truncations-exist
  pt = PR-gives-existence-of-truncations (hfunext-gives-dfunext hfe) ρ

  open basic-truncation-development pt hfe -- using (∨-is-subsingleton; ∃)
  open powerset-union-existence pt hfe

  ⋃ : {X : 𝓤 ̇} → 𝓟𝓟 X → 𝓟 X
  ⋃ 𝓐 = pr₁ (PR-gives-existence-of-unions ρ _ 𝓐)

  ⋃-property : {X : 𝓤 ̇}
               (𝓐 : 𝓟𝓟 X) → (x : X)
           -------------------------------------------------
   →       (x ∈ ⋃ 𝓐)  ⇔  (∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A))

  ⋃-property 𝓐 = pr₂ (PR-gives-existence-of-unions ρ _ 𝓐)

  --"The construction of intersections is as that of unions using propositional resizing:
  intersections-exist : (X : 𝓤 ̇) (𝓐 : 𝓟𝓟 X)
   →   Σ B ꞉ 𝓟 X , ((x : X) → (x ∈ B) ⇔ ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A))
  intersections-exist {𝓤} X 𝓐 = B , γ
    where
     β : X → 𝓤 ⁺ ̇
     β x = (A : 𝓟 X) → A ∈ 𝓐 → x ∈ A

     βx✧ : (x : X) → is-subsingleton (β x)
     βx✧ x = Π-is-subsingleton hunapply (λ A → Π-is-subsingleton hunapply
                                         (λ _ → ∈-is-subsingleton A x))

     B : 𝓟 X
     B x = resize ρ (β x) (βx✧ x) , resize-is-subsingleton ρ (β x) (βx✧ x)

     γ : (x : X) → (x ∈ B) ⇔ ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A)
     γ = λ x → from-resize ρ (β x) (βx✧ x) , to-resize ρ (β x) (βx✧ x)


  ⋂ : {X : 𝓤 ̇} → 𝓟𝓟 X → 𝓟 X
  ⋂ {𝓤} {X} 𝓐 = pr₁ (intersections-exist X 𝓐)

  ⋂-property : {X : 𝓤 ̇} (𝓐 : 𝓟𝓟 X) → (x : X)
             -------------------------------------------
   →        (x ∈ ⋂ 𝓐)  ⇔  ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A)

  ⋂-property {𝓤} {X} 𝓐 = pr₂ (intersections-exist X 𝓐)

  ∅ full : {X : 𝓤 ̇} → 𝓟 X
  ∅ x = Lift _ 𝟘 , equiv-to-subsingleton (Lift-≃ 𝟘) 𝟘-is-subsingleton
  full x = Lift _ 𝟙 , equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton

  ∅-property : (X : 𝓤 ̇) → (x : X) → ¬ (x ∈ ∅)
  ∅-property X x = lower

  full-property : (X : 𝓤 ̇) → (x : X) → x ∈ full
  full-property X x = lift ⋆

  _∩_ _∪_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓟 X

  A ∪ B = λ x → ((x ∈ A) ∨ (x ∈ B)) , ∨-is-subsingleton

  A ∩ B = λ x → ((x ∈ A) × (x ∈ B)) ,
                 ×-is-subsingleton (∈-is-subsingleton A x) (∈-is-subsingleton B x)

  ∪-property :   {X : 𝓤 ̇ } (A B : 𝓟 X) (x : X)
                -----------------------------------
   →             x ∈ (A ∪ B)  ⇔  (x ∈ A) ∨ (x ∈ B)

  ∪-property {𝓤} {X} A B x = id , id

  ∩-property : {X : 𝓤 ̇}(A B : 𝓟 X) (x : X)
              --------------------------------
   →          x ∈ (A ∩ B)  ⇔  (x ∈ A) × (x ∈ B)

  ∩-property {𝓤} {X} A B x = id , id

  infix  20 _∩_
  infix  20 _∪_

