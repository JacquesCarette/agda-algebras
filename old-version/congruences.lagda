---
layout: default
title : congruences module (of the Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: congruences.lagda
AUTHOR: William DeMeo and Siva Somayyajula
DATE: 30 Jun 2020
NOTE: This file used to be called relations.agda
-->

## Congruences in Agda (congruences.lagda)

### Options, imports

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext)

module congruences {𝑆 : Signature 𝓞 𝓥} {gfe : global-dfunext} where

open import prelude using (Univalence; is-prop; 𝟙; _≡⟨_⟩_; _∎; refl; _⁻¹; funext; ap; _∙_; Pred₀; ≡-sym; ≡-trans;
 ≡-rfl; 𝓇ℯ𝒻𝓁; cong-app-pred; id; _⇔_; _∈₀_; _⊆₀_; 𝓟; ∈₀-is-subsingleton; is-subsingleton; equiv-to-subsingleton;
 powersets-are-sets'; subset-extensionality'; propext; Ω; Σ-is-subsingleton; Π-is-subsingleton; _⊇_; _⊆_; _=̇_;
 Pred-=̇-≡; cong-app-𝓟; fst; snd; ≡-elim-left; to-Σ-≡; transport) public
\end{code}

### Binary relations, kernels

\begin{code}
module _ {𝓤 𝓡 : Universe} where

 REL : 𝓤 ̇ → 𝓡 ̇ → (𝓝 : Universe) → (𝓤 ⊔ 𝓡 ⊔ 𝓝 ⁺) ̇
 REL A B 𝓝 = A → B → 𝓝 ̇

 KER : {A : 𝓤 ̇ } {B : 𝓡 ̇ } → (A → B) → 𝓤 ⊔ 𝓡 ̇
 KER {A} g = Σ x ꞉ A , Σ y ꞉ A , g x ≡ g y

 KER-pred : {A : 𝓤 ̇}{B : 𝓡 ̇} → (A → B) → Pred (A × A) 𝓡
 KER-pred g (x , y) = g x ≡ g y

Rel : {𝓤 : Universe} → 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
Rel A 𝓝 = REL A A 𝓝

Rel₀ : {𝓤 : Universe} → 𝓤 ̇ → (𝓝 : Universe) → 𝓤 ⊔ 𝓝 ⁺ ̇
Rel₀ A 𝓝 = Σ P ꞉ (A → A → 𝓝 ̇) , ∀ x y → is-subsingleton (P x y)

KER-rel : {𝓤 𝓡 : Universe}{A : 𝓤 ̇ } {B : 𝓡 ̇ } → (A → B) → Rel A 𝓡
KER-rel g x y = g x ≡ g y
\end{code}

#### Examples

\begin{code}
module _ {𝓤 : Universe} where
 ker : {A B : 𝓤 ̇ } → (A → B) → 𝓤 ̇
 ker = KER{𝓤}{𝓤}

 ker-rel : {A B : 𝓤 ̇ } → (A → B) → Rel A 𝓤
 ker-rel = KER-rel {𝓤} {𝓤}

 ker-pred : {A B : 𝓤 ̇ } → (A → B) → Pred (A × A) 𝓤
 ker-pred = KER-pred {𝓤} {𝓤}

 --The identity relation.
 𝟎 : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎 {A} = Σ a ꞉ A , Σ b ꞉ A , a ≡ b

 --...on the domain of an algebra...
 𝟎-alg-rel : {𝑆 : Signature 𝓞 𝓥}{𝑨 : Algebra 𝓤 𝑆} → 𝓤 ̇
 𝟎-alg-rel {𝑨 = 𝑨} = Σ a ꞉ ∣ 𝑨 ∣ , Σ b ꞉ ∣ 𝑨 ∣ , a ≡ b

 --...as a binary relation...
 𝟎-rel : {A : 𝓤 ̇ } → Rel A 𝓤
 𝟎-rel a b = a ≡ b

 --...as a binary predicate...
 𝟎-pred : {A : 𝓤 ̇ } → Pred (A × A) 𝓤
 𝟎-pred (a , a') = a ≡ a'

 𝟎-pred' : {A : 𝓤 ̇ } → 𝓤 ̇
 𝟎-pred' {A} = Σ p ꞉ (A × A) , ∣ p ∣ ≡ ∥ p ∥

 𝟏 : {A : 𝓤 ̇ } → Rel A 𝓤₀
 𝟏 a b = 𝟙
\end{code}

### Properties of binary relations

\begin{code}
module _ {𝓤 𝓡 : Universe} where

 reflexive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 reflexive _≈_ = ∀ x → x ≈ x

 symmetric : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 symmetric _≈_ = ∀ x y → x ≈ y → y ≈ x

 transitive : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

 is-subsingleton-valued : {A : 𝓤 ̇ } → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-subsingleton-valued  _≈_ = ∀ x y → is-prop (x ≈ y)
\end{code}

### Equivalence relations

\begin{code}
 record IsEquivalence {A : 𝓤 ̇ } (_≈_ : Rel A 𝓡) : 𝓤 ⊔ 𝓡 ̇ where
   field
     rfl  : reflexive _≈_
     sym   : symmetric _≈_
     trans : transitive _≈_

 is-equivalence-relation : {X : 𝓤 ̇ } → Rel X 𝓡 → 𝓤 ⊔ 𝓡 ̇
 is-equivalence-relation _≈_ =
  is-subsingleton-valued _≈_
   × reflexive _≈_ × symmetric _≈_ × transitive _≈_

module _ {𝓤 : Universe} where
 𝟎-IsEquivalence : {A : 𝓤 ̇ } → IsEquivalence{𝓤 = 𝓤}{A = A} 𝟎-rel
 𝟎-IsEquivalence = record { rfl = λ x → 𝓇ℯ𝒻𝓁
                          ; sym = λ x y x≡y → x≡y ⁻¹
                          ; trans = λ x y z x≡y y≡z → x≡y ∙ y≡z }

 ≡-IsEquivalence : {X : 𝓤 ̇} → IsEquivalence{𝓤}{𝓤}{X} _≡_
 ≡-IsEquivalence = record { rfl = ≡-rfl ; sym = ≡-sym ; trans = ≡-trans }


map-kernel-IsEquivalence : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇}
                           (f : A → B) → IsEquivalence (KER-rel f)

map-kernel-IsEquivalence {𝓤}{𝓦} f =
 record { rfl = λ x → 𝓇ℯ𝒻𝓁
        ; sym = λ x y x₁ → ≡-sym{𝓦} (f x) (f y) x₁
        ; trans = λ x y z x₁ x₂ → ≡-trans (f x) (f y) (f z) x₁ x₂ }
\end{code}

### Classes and quotients

\begin{code}
module relation-predicate-classes {𝓤 𝓡 : Universe} where

 -- relation class
 [_] : {A : 𝓤 ̇ } → A → Rel A 𝓡 → Pred A 𝓡
 [ a ] R = λ x → R a x

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 []-elim : {A : 𝓤 ̇ }{a x : A}{R : Rel A 𝓡}
  →         R a x ⇔ (x ∈ [ a ] R)
 []-elim = id , id

 𝒜 : {A : 𝓤 ̇}{R : Rel A 𝓡} → Pred A 𝓡 → (𝓤 ⊔ 𝓡 ⁺) ̇
 𝒜 {A}{R} = λ (C : Pred A 𝓡) → Σ a ꞉ A , C ≡ ( [ a ] R)

 -- relation quotient (predicate version)
 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓡 → 𝓤 ⊔ (𝓡 ⁺) ̇
 A / R = Σ C ꞉ Pred A 𝓡 ,  𝒜{A}{R} C
 -- old version:  A / R = Σ C ꞉ Pred A 𝓡 ,  Σ a ꞉ A ,  C ≡ ( [ a ] R )

 -- For a reflexive relation, we have the following elimination rule.
 /-refl : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   reflexive R → [ a ] R ≡ [ a' ] R → R a a'
 /-refl{A = A}{a}{a'}{R} rfl x  = γ
  where
   a'in : a' ∈ [ a' ] R
   a'in = rfl a'
   γ : a' ∈ [ a ] R
   γ = cong-app-pred a' a'in (x ⁻¹)

 /-refl' : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   transitive R → R a' a → ([ a ] R) ⊆ ([ a' ] R)
 /-refl'{A = A}{a}{a'}{R} trn Ra'a {x} aRx = trn a' a x Ra'a aRx 

 ⌜_⌝ : {A : 𝓤 ̇}{R : Rel A 𝓡} → A / R  → A
 ⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

 -- introduction rule for relation class with designated representative
 ⟦_⟧ : {A : 𝓤 ̇} → A → {R : Rel A 𝓡} → A / R
 ⟦ a ⟧ {R} = ([ a ] R) , a , 𝓇ℯ𝒻𝓁

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 ⟦⟧-elim : {A : 𝓤 ̇ }{a x : A}{R : Rel A 𝓡}
  →         R a x ⇔ (x ∈ [ a ] R)
 ⟦⟧-elim = id , id

 -- elimination rule for relation class representative
 /-Refl : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   reflexive R → ⟦ a ⟧{R} ≡ ⟦ a' ⟧ → R a a'
 /-Refl rfl (refl _)  = rfl _

 open IsEquivalence{𝓤}{𝓡}

 /-subset : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) ⊆ ([ a' ] R)
 /-subset {A = A}{a}{a'}{R} Req Raa' {x} Rax = (trans Req) a' a x (sym Req a a' Raa') Rax 

 /-supset : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) ⊇ ([ a' ] R)
 /-supset {A = A}{a}{a'}{R} Req Raa' {x} Ra'x = (trans Req) a a' x Raa' Ra'x

 /-=̇ : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   IsEquivalence R → R a a' → ([ a ] R) =̇ ([ a' ] R)
 /-=̇ {A = A}{a}{a'}{R} Req Raa' = /-subset Req Raa' , /-supset Req Raa'
\end{code}

### Quotient extensionality

We need a (subsingleton) identity type for congruence classes over sets so that we can equate two classes even when they are presented using different representatives.  For this we assume that our relations are on sets, rather than arbitrary types.  For us, this is equivalent to assuming that there is at most one proof that two elements of a set are the same.  In other words, a set is a type with *unique identity proofs*. As a general principle, this is sometimes referred to as "proof irrelevance"---two proofs of a single identity are equal.

\begin{code}
 class-extensionality : propext 𝓡 → global-dfunext
  →       {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →       (∀ a x → is-subsingleton (R a x))
  →       IsEquivalence R
         ---------------------------------------
  →        R a a' → ([ a ] R) ≡ ([ a' ] R)

 class-extensionality pe gfe {A = A}{a}{a'}{R} ssR Req Raa' =
  Pred-=̇-≡ pe gfe {A}{[ a ] R}{[ a' ] R} (ssR a) (ssR a') (/-=̇ Req Raa')

 to-subtype-⟦⟧ : {A : 𝓤 ̇}{R : Rel A 𝓡}{C D : Pred A 𝓡}
                 {c : 𝒜{A}{R} C}{d : 𝒜{A}{R} D}
  →              (∀ C → is-subsingleton (𝒜{A}{R} C))
  →              C ≡ D  →  (C , c) ≡ (D , d)

 to-subtype-⟦⟧ {D = D}{c}{d} ssA CD = to-Σ-≡ (CD , ssA D (transport 𝒜 CD c) d)

 class-extensionality' : propext 𝓡 → global-dfunext
  →       {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →       (∀ a x → is-subsingleton (R a x))
  →       (∀ C → is-subsingleton (𝒜{A}{R} C))
  →       IsEquivalence R
         ---------------------------------------
  →        R a a' → (⟦ a ⟧ {R}) ≡ (⟦ a' ⟧ {R})

 class-extensionality' pe gfe {A = A}{a}{a'}{R} ssR ssA Req Raa' = γ
  where
   CD : ([ a ] R) ≡ ([ a' ] R)
   CD = class-extensionality pe gfe {A}{a}{a'}{R} ssR Req Raa'

   γ : (⟦ a ⟧ {R}) ≡ (⟦ a' ⟧ {R})
   γ = to-subtype-⟦⟧ ssA CD

\end{code}

#### sugar

\begin{code}
_on_ : {𝓤 𝓥 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓥 ̇}{C : 𝓦 ̇}
 →     (B → B → C) → (A → B) → (A → A → C)

_*_ on g = λ x y → g x * g y


_⇒_ : {𝓤 𝓥 𝓦 𝓧 : Universe}{A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →    REL A B 𝓦 → REL A B 𝓧 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ̇

P ⇒ Q = ∀ {i j} → P i j → Q i j

infixr 4 _⇒_


_=[_]⇒_ : {𝓤 𝓥 𝓡 𝓢 : Universe}{A : 𝓤 ̇ } {B : 𝓥 ̇ }
 →        Rel A 𝓡 → (A → B) → Rel B 𝓢 → 𝓤 ⊔ 𝓡 ⊔ 𝓢 ̇

P =[ g ]⇒ Q = P ⇒ (Q on g)

infixr 4 _=[_]⇒_
\end{code}

### Compatibility

\begin{code}
module _ {𝓤 𝓥 𝓦 : Universe} {γ : 𝓥 ̇ } {Z : 𝓤 ̇ } where

 lift-rel : Rel Z 𝓦 → (γ → Z) → (γ → Z) → 𝓥 ⊔ 𝓦 ̇
 lift-rel R f g = ∀ x → R (f x) (g x)

 compatible-fun : (f : (γ → Z) → Z)(R : Rel Z 𝓦) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 compatible-fun f R  = (lift-rel R) =[ f ]⇒ R

-- relation compatible with an operation
compatible-op : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} → ∣ 𝑆 ∣ → Rel ∣ 𝑨 ∣ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
compatible-op {𝑨 = 𝑨} f R = ∀{𝒂}{𝒃} → (lift-rel R) 𝒂 𝒃  → R ((f ̂ 𝑨) 𝒂) ((f ̂ 𝑨) 𝒃)
-- alternative notation: (lift-rel R) =[ f ̂ 𝑨 ]⇒ R

--The given relation is compatible with all ops of an algebra.
compatible : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆) → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
compatible {𝓤 = 𝓤}{𝓦 = 𝓦} 𝑨 R = ∀ f → compatible-op{𝓤 = 𝓤}{𝓦 = 𝓦}{𝑨 = 𝑨} f R
\end{code}

#### Examples

\begin{code}
𝟎-compatible-op : funext 𝓥 𝓤 → {𝑨 : Algebra 𝓤 𝑆} (f : ∣ 𝑆 ∣)
 →                   compatible-op {𝓤 = 𝓤}{𝑨 = 𝑨} f 𝟎-rel
𝟎-compatible-op fe {𝑨} f ptws0  = ap (f ̂ 𝑨) (fe (λ x → ptws0 x))

𝟎-compatible : funext 𝓥 𝓤 → {A : Algebra 𝓤 𝑆} → compatible A 𝟎-rel
𝟎-compatible fe {A} = λ f args → 𝟎-compatible-op fe {A} f args
\end{code}

### Congruences and quotient algebras

\begin{code}
Con : (A : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
Con {𝓤} A = Σ θ ꞉ ( Rel ∣ A ∣ 𝓤 ) , IsEquivalence θ × compatible A θ

con : (A : Algebra 𝓤 𝑆)  →  Pred (Rel ∣ A ∣ 𝓤) (𝓞 ⊔ 𝓥 ⊔ 𝓤)
con A = λ θ → IsEquivalence θ × compatible A θ

record Congruence {𝓤 𝓦 : Universe} (A : Algebra 𝓤 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇  where
 constructor mkcon
 field
  ⟨_⟩ : Rel ∣ A ∣ 𝓦
  Compatible : compatible A ⟨_⟩
  IsEquiv : IsEquivalence ⟨_⟩

open Congruence

compatible-equivalence : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓤 𝑆} → Rel ∣ 𝑨 ∣ 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ̇
compatible-equivalence {𝓤}{𝓦} {𝑨} R = compatible 𝑨 R × IsEquivalence R

-- Example
Δ : funext 𝓥 𝓤 → (A : Algebra 𝓤 𝑆) → Congruence A
Δ fe A = mkcon 𝟎-rel ( 𝟎-compatible fe ) ( 𝟎-IsEquivalence )


module congruence-predicates {𝓤 𝓡 : Universe} where

 open relation-predicate-classes {𝓤}{𝓡}

 _╱_ : (A : Algebra 𝓤 𝑆) -- type ╱ with `\---` plus `C-f`
  →      Congruence{𝓤}{𝓡} A               -- a number of times, then `\_p`
        -----------------------
  →     Algebra (𝓤 ⊔ 𝓡 ⁺) 𝑆
 A ╱ θ = (( ∣ A ∣ / ⟨ θ ⟩ ) , -- carrier (i.e. domain or universe))
           (λ f args         -- operations
            → ([ (f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩) ,
              ((f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
           )
         )

 Zero╱ : {A : Algebra 𝓤 𝑆} → (θ : Congruence{𝓤}{𝓡} A) → Rel (∣ A ∣ / ⟨ θ ⟩) (𝓤 ⊔ 𝓡 ⁺)
 Zero╱ θ = λ x x₁ → x ≡ x₁

 ╱-refl : (A : Algebra 𝓤 𝑆){θ : Congruence{𝓤}{𝓡} A}{a a' : ∣ A ∣}
  →   ⟦ a ⟧{⟨ θ ⟩} ≡ ⟦ a' ⟧ → ⟨ θ ⟩ a a'
 ╱-refl A {θ} (refl _)  = IsEquivalence.rfl (IsEquiv θ) _
\end{code}

#### Dead code

We're not using any of the code below, so we may remove it eventually.

We currently use the relation-predicate-classes and congruence-predicates modules above.

\begin{code}
module relation-classes {𝓤 𝓡 : Universe} where

 -- relation class
 [_]_ :  {A : 𝓤 ̇ } → A → Rel A 𝓡 → 𝓤 ⊔ 𝓡 ̇
 [ a ] R = Σ x ꞉ _ , R a x

 -- relation quotient
 _/_ : (A : 𝓤 ̇ ) → Rel A 𝓡 → (𝓤 ⊔ 𝓡) ⁺ ̇
 A / R = Σ C ꞉ _ ,  Σ a ꞉ A ,  C ≡ ( [ a ] R )

 -- get relation class representative
 ⌜_⌝ : {A : 𝓤 ̇}{R : Rel A 𝓡} → A / R  → A
 ⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

 -- intro rule for relation class with designated representative
 ⟦_⟧ : {A : 𝓤 ̇} → A → {R : Rel A 𝓡} → A / R
 ⟦ a ⟧ {R} = ([ a ] R) , a , 𝓇ℯ𝒻𝓁

 -- elimination rule for relation class representative
 /-Refl : {A : 𝓤 ̇}{a a' : A}{R : Rel A 𝓡}
  →   reflexive R → ⟦ a ⟧{R} ≡ ⟦ a' ⟧ → R a a'
 /-Refl rfl (refl _)  = rfl _


module congruence-relations where
 open relation-classes

 _╱_ : {𝓤 𝓧 : Universe}(A : Algebra 𝓤 𝑆) -- type ╱ᵣ as `\---` plus
  →      Congruence{𝓤}{𝓧} A                -- C-f a number of times, then `\_r`
        ------------------------
  →      Algebra (𝓤 ⁺ ⊔ 𝓧 ⁺) 𝑆

 A ╱ θ = (( ∣ A ∣ / ⟨ θ ⟩ ) , -- carrier (i.e. domain or universe))
           (λ f args         -- operations
            → ([ (f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) ] ⟨ θ ⟩) ,
              ((f ̂ A) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
           )
         )

 Zero/ : {𝓤 𝓧 : Universe}{A : Algebra 𝓤 𝑆} → (θ : Congruence{𝓤}{𝓧} A) → Rel (∣ A ∣ / ⟨ θ ⟩) (𝓤 ⁺ ⊔ 𝓧 ⁺)
 Zero/ θ = λ x x₁ → x ≡ x₁

 /-refl : {𝓤 𝓧 : Universe}(A : Algebra 𝓤 𝑆){θ : Congruence{𝓤}{𝓧} A}{a a' : ∣ A ∣}
  →   ⟦ a ⟧{⟨ θ ⟩} ≡ ⟦ a' ⟧ → ⟨ θ ⟩ a a'
 /-refl A {θ} (refl _)  = IsEquivalence.rfl (IsEquiv θ) _


module relation-powerset-classes {𝓤 : Universe} where
 -- Properties of binary relations as powersets --------------------------------------

 record SetRel (A : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor mksetrel
  field
    ⟨_⟩ : 𝓟(A × A)
    isset : is-set A

 open SetRel

 SetRel→Rel : {A : 𝓤 ̇}(R : SetRel A) → Rel A 𝓤
 SetRel→Rel {A} R = λ a a' → ∣ ⟨ R ⟩  (a , a') ∣

 Rel₀→𝓟² : {A : 𝓤 ̇}{R : Rel₀ A 𝓤} → 𝓟(A × A)
 Rel₀→𝓟² {A}{R} (x , y) = ∣ R ∣ x y , ∥ R ∥ x y

 Pred₀→𝓟² : {A : 𝓤 ̇}{P : Pred₀ (A × A) 𝓤} → 𝓟(A × A)
 Pred₀→𝓟² {A}{P} aa = ∣ P ∣ aa , ∥ P ∥ aa

 Rel₀→SetRel : {A : 𝓤 ̇}{R : Rel₀ A 𝓤} → is-set A → SetRel A
 Rel₀→SetRel {A}{R} Aset = mksetrel (Rel₀→𝓟²{A}{R}) Aset

 Pred₀→SetRel : {A : 𝓤 ̇}{P : Pred₀ (A × A) 𝓤} → is-set A → SetRel A
 Pred₀→SetRel {A}{P} Aset = mksetrel (Pred₀→𝓟²{A}{P}) Aset


 module _ {A : 𝓤 ̇} where

  refl𝓟 : SetRel A → 𝓤 ̇
  refl𝓟 θ = ∀ x → (x , x) ∈₀ (⟨ θ ⟩)

  symm𝓟 : SetRel A → 𝓤 ̇
  symm𝓟 θ = ∀ x y → (x , y) ∈₀ (⟨ θ ⟩)  → (y , x) ∈₀ (⟨ θ ⟩)

  trans𝓟 : SetRel A → 𝓤 ̇
  trans𝓟 θ = ∀ x y z → (x , y) ∈₀ (⟨ θ ⟩) → (y , z) ∈₀ (⟨ θ ⟩) → (x , z) ∈₀ (⟨ θ ⟩)

  is-subsingleton-valued-𝓟 : SetRel A → 𝓤 ̇
  is-subsingleton-valued-𝓟 θ = ∀ x y → is-prop ((x , y) ∈₀ (⟨ θ ⟩))

  -- setrel class
  _/_ : A → (θ : SetRel A) → 𝓟 A
  a / θ  = λ x → ((a , x) ∈₀ (⟨ θ ⟩)) , (∈₀-is-subsingleton (⟨ θ ⟩) (a , x))

  --So, x ∈ [ a ] iff ⟨ R ⟩ a x; thus the following elimination rule is a tautology.
  /-elim : {a x : A}{θ : SetRel A}
   →       (a , x) ∈₀ (⟨ θ ⟩) ⇔ (x ∈₀ (a / θ))
  /-elim = id , id

  -- For a reflexive relation, we have the following elimination rule.
  /-refl : {a a' : A}{θ : SetRel A}
   →       refl𝓟 θ → (a / θ) ≡ (a' / θ) → (a , a') ∈₀ (⟨ θ ⟩)
  /-refl {a}{a'}{θ} rfl x  = γ
   where
    a'in : a' ∈₀ (a' / θ)
    a'in = rfl a'
    γ : a' ∈₀ (a / θ)
    γ = cong-app-𝓟 a' a'in (x ⁻¹)

 -- relation quotient (powerset version)
 _/̇_ : (A : 𝓤 ̇) → SetRel A → 𝓤 ⁺ ̇        -- type /̇ with `/\^.`
 A /̇ θ = Σ C ꞉ (𝓟 A) , Σ a ꞉ A , C ≡ (a / θ)

 ⌜_⌝ : {A : 𝓤 ̇}{θ : SetRel A} → A /̇ θ  → A
 ⌜ 𝒂 ⌝ = ∣ ∥ 𝒂 ∥ ∣    -- type ⌜ and ⌝ as `\cul` and `\cur`

 -- introduction rule for relation class with designated representative
 ⟦_⟧ : {A : 𝓤 ̇} → A → {θ : SetRel A} → A /̇ θ
 ⟦ a ⟧ {θ} = (a / θ) , a , 𝓇ℯ𝒻𝓁

 --So, x ∈ [ a ]ₚ R iff R a x, and the following elimination rule is a tautology.
 ⟦⟧-elim : {A : 𝓤 ̇ }{θ : SetRel A}{a x : A}
  →         (a , x) ∈₀ (⟨ θ ⟩)  ⇔  x ∈₀ (a / θ)
 ⟦⟧-elim = id , id

 ⟦⟧→[]-agreement : {A : 𝓤 ̇}{θ : SetRel A}{x y : A}
  →                (⟦ x ⟧ {θ} ≡ ⟦ y ⟧{θ})  →  ((x / θ) ≡ (y / θ))
 ⟦⟧→[]-agreement equ = ap fst equ

 record SetRel-IsEquivalence {A : 𝓤 ̇ } (R : SetRel A) : 𝓤 ⁺ ̇ where
  field
    rfl  : refl𝓟 R
    sym   : symm𝓟 R
    trans : trans𝓟 R

module congruence-relations-powersets where

 open relation-powerset-classes
 open SetRel

 SetCon : {𝓤 : Universe} (A : Algebra 𝓤 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 SetCon {𝓤} 𝑨 = Σ θ ꞉ ( SetRel ∣ 𝑨 ∣ ) , SetRel-IsEquivalence θ × compatible{𝓤}{𝓤} 𝑨 (SetRel→Rel θ)

 record SetCongruence {𝓤 : Universe} (𝑨 : Algebra 𝓤 𝑆) : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇  where
  constructor mksetcon
  field
   ⟪_⟫ : SetRel ∣ 𝑨 ∣ -- 𝓟(∣ 𝑨 ∣ × ∣ 𝑨 ∣) --⟨_⟩ : Rel ∣ A ∣ 𝓤
   Compatible : compatible 𝑨 (SetRel→Rel ⟪_⟫)
   IsEquiv : SetRel-IsEquivalence ⟪_⟫

 open SetCongruence

 _╱_ : {𝓤 : Universe} (𝑨 : Algebra 𝓤 𝑆)   -- type ╱ with `\---` plus `C-f`
  →     SetCongruence 𝑨                 -- a number of times
       ----------------------
  →     Algebra (𝓤 ⁺) 𝑆

 𝑨 ╱ θ = (( ∣ 𝑨 ∣ /̇ ⟪ θ ⟫ ) , -- carrier (i.e. domain or universe))
           (λ f args         -- operations
            → (((f ̂ 𝑨)(λ i₁ → ∣ ∥ args i₁ ∥ ∣)) / ⟪ θ ⟫) , (f ̂ 𝑨) (λ i₁ → ∣ ∥ args i₁ ∥ ∣) , refl _ )
           )

 ╱-refl : {𝓤 : Universe} (𝑨 : Algebra 𝓤 𝑆){θ : SetCongruence 𝑨}{a a' : ∣ 𝑨 ∣}
  →   ⟦ a ⟧{⟪ θ ⟫} ≡ ⟦ a' ⟧{⟪ θ ⟫} → (a , a') ∈₀ ⟨ ⟪ θ ⟫ ⟩
 ╱-refl _ {θ} (refl _)  = SetRel-IsEquivalence.rfl (IsEquiv θ) _
\end{code}

