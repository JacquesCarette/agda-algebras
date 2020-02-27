--File: Basic.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 21 Feb 2020
--Notes: Based on the file `basic.agda` (24 Dec 2019).
--       Used for 1st half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
  using (Level; lzero; lsuc;_⊔_; ∃; _,_; ⊥; Bool; _×_; ∣_∣; ⟦_⟧; _≡_; proj₁; proj₂; _∘_; Pred; _∈_)

module Basic where

-- Operations and projections
module _ {i j} where
  Op : Set i → Set j → Set (i ⊔ j)
  Op I A = (I → A) → A

  π : {I : Set i} {A : Set j} → I → Op I A
  π i x = x i

-- i is the universe in which the operation symbols lives
-- j is the universe in which the arities live
Signature : (i j : Level) → Set (lsuc (i ⊔ j))
Signature i j = ∃ λ (F : Set i) → F → Set j

private
  variable
    i j : Level

-- k is the universe in which the operational type lives
Algebra : (k : Level)  ->  Signature i j
          -------------------------------
  ->      Set (i ⊔ j ⊔ lsuc k)
Algebra k (𝐹 , ρ) =
  ∃ λ (A : Set k) -> (𝓸 : 𝐹) -> Op (ρ 𝓸) A

private
  variable
    k l m : Level
    S : Signature i j

-- Indexed product of algebras is an algebra
-- The trick is to view the Pi-type as a dependent product i.e.
-- A i1 × A i2 × A i3 × ... = (i : I) → A i
Π : {I : Set m} → (I → Algebra k S) → Algebra (k ⊔ m) S
Π {I = I} A = ((i : I) → ∣ A i ∣) , λ 𝓸 x i → ⟦ A i ⟧ 𝓸 λ j → x j i

-- Subalgebras
module _ {i j k l : Level} {S : Signature i j} where
  data _is-supalgebra-of_ (A : Algebra k S) : Pred (Algebra (k ⊔ l) S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    mem : {P : Pred ∣ A ∣ l} {B : (o : ∣ S ∣) -> Op (⟦ S ⟧ o) (∃ P)} →
            ((o : ∣ S ∣) → (x : ⟦ S ⟧ o → ∃ P) →
              ∣ B o x ∣ ≡ ⟦ A ⟧ o (λ i → ∣ x i ∣)) →
          A is-supalgebra-of (∃ P , B)

  _is-subalgebra-of_ : Algebra _ S → Algebra _ S → Set _
  B is-subalgebra-of A = A is-supalgebra-of B

{-data Su {i j k l} {s : Signature i j} (K : Pred (Algebra k s) l) : Pred (Algebra k s) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  sbase : {A : Algebra k s} → A ∈ K → A ∈ Su K
  sub : ∀ {A : Algebra k s} {B : Algebra k s} → A ∈ Su K → B is-subalgebra-of A → B ∈ Su K
-}

-- Homomorphic images are canonically algebras since they are subuniverses
-- 
-- SubunivAlg (hom-image-is-sub f)

data P {i j k l} {S : Signature i j} (K : Pred (Algebra k S) l) :
  Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    pbase : {A : Algebra k S} → A ∈ K → A ∈ P K
    prod : {I : Set k} {A : I → Algebra k S} → (∀ i → A i ∈ P K) → Π A ∈ P K

--Example: monoid
--  A monoid signature has two operation symbols, say, `e`
--  and `·`, of arities 0 and 2, of types `(Empty -> A) -> A` and
--  `(Bool -> A) -> A`, resp. The types indicate that `e` is
--  nullary (i.e., takes no args, equivalently, takes args of
--  type `Empty -> A`), while `·` is binary, as indicated by
--  argument type `Bool -> A`.

data monoid-op : Set where
  e : monoid-op
  · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → ⊥; · → Bool }
