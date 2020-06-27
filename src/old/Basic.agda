--File: Basic.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 21 Feb 2020
--Notes: Based on the file `basic.agda` (24 Dec 2019).
--       Used for 1st half of talk at JMM Special Session (Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries  using (Level; lzero; lsuc;_⊔_; ∃; _,_; ⊥; Bool; _×_; ∣_∣; ⟦_⟧; _≡_; _∘_; Pred; _∈_; Lift)
-- open import Universe using (Universe; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; _⁺; _̇;_⊔_)
--; universe-of; id; 𝑖𝑑; _∘_; _,_; Σ; -Σ; pr₁; pr₂; Π; -Π; domain; _×_; _≡_; refl; _∼_; transport; _≡⟨_⟩_; _∎; ap; _∙_; _⁻¹; _⇔_; _iff_; lr-implication; rl-implication)


module Basic where

-- -- Operations and projections
module _ {i j} where
  Op : Set i → Set j → Set (i ⊔ j)
  Op I A = (I → A) → A

  π : {I : Set i} {A : Set j} → I → Op I A
  π i x = x i

-- i is the universe in which the operation symbols lives
-- j is the universe in which the arities live
Signature : (i j : Level) → Set _
Signature i j = ∃ λ (F : Set i) → F → Set j

private
  variable
    i j : Level

-- k is the universe in which the operational type lives
Algebra : (k : Level)  ->  Signature i j
          -------------------------------
  ->      Set _
Algebra k S =
  ∃ λ (A : Set k) -> (𝓸 : ∣ S ∣) -> Op (⟦ S ⟧ 𝓸) A

private
  variable
    k l m : Level
    S : Signature i j

-- Indexed product of algebras is an algebra
-- The trick is to view the Pi-type as a dependent product i.e.
-- A i1 × A i2 × A i3 × ... = (i : I) → A i
Π : {I : Set m} → (I → Algebra k S) → Algebra (k ⊔ m) S
Π {I = I} A = ((i : I) → ∣ A i ∣) , λ 𝓸 x i → ⟦ A i ⟧ 𝓸 λ j → x j i

--Example: monoid
--  A monoid signature has two operation symbols, say, `e`
--  and `·`, of arities 0 and 2, of types `(Empty -> A) -> A`
--  and `(Bool -> A) -> A`, resp. The types indicate that `e`
--  is nullary (i.e., takes no args, equivalently, takes args
--  of type `Empty -> A`), while `·` is binary, as indicated
--  by argument type `Bool -> A`.

data monoid-op : Set where
  e : monoid-op
  · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → ⊥; · → Bool }

-- Binary product of algebras
-- _⊗_ : Algebra k S -> Algebra k S -> Algebra k S
-- 𝑨 ⊗ 𝑩 = (∣ 𝑨 ∣ × ∣ 𝑩 ∣) , λ 𝓸 x → ( ⟦ 𝑨 ⟧ 𝓸 (λ i -> ∣ x i ∣ ) , ⟦ 𝑩 ⟧ 𝓸 (λ i -> ⟦ x i ⟧ ) )
-- (let's reserve ⊗ for tensor product)