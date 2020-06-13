--FILE: UF-Import_all.agda
--DATE: 2020 May 6
--BLAME: williamdemeo@gmail.com
--DESCR: List of almost all definitions.  This is useful when searching around for stuff that we may to use in an import statement.

-- UF-Prelude.agda
-- UF-Singleton.agda
-- UF-Monoid.agda
-- UF-Equality.agda
-- UF-Univalence.agda
-- UF-Extensionality.agda
-- UF-Embedding.agda
-- UF-Truncation.agda
-- UF-Choice.agda
-- UF-Structures.agda
-- UF-MetricSpaces.agda

module UF-Import_all where

open import UF-Prelude using (Universe; 𝓤₀; 𝓤; 𝓥; 𝓦; _̇; _⊔_; _⁺; 𝟙; ⋆; 𝟙-induction; 𝟙-recursion; !𝟙; 𝟘; 𝟘-induction; 𝟘-recursion; !𝟘; is-empty; ¬; ℕ; zero; succ; ℕ-induction; ℕ-recursion; ℕ-iteration; id; 𝑖𝑑; _+_; inl; inr; +-induction; +-intro; +-recursion; 𝟚; ₀; ₁; 𝟚-induction; 𝟚-induction'; _,_; Σ; pr₁; pr₂; -Σ; Σ-induction; curry; _×_; Π; -Π; _∘_; domain; codomain; type-of; Id; refl; _≡_; ≡-sym; 𝕁; ≡-induction; transport; transport𝕁; lhs; rhs; _∙_; _≡⟨_⟩_; _∎; _⁻¹; rdnel; rdner; ap; _∼_; transport-×; transportd; transport-Σ; ¬¬; ¬¬¬; dni; ¬¬-intro; contrapositive; tno; ¬¬¬-elim; _⇔_; _iff_; lr-implication; iff-elim-left; rl-implication; iff-elim-right; absurdity³-is-absurdity; _≢_; ≢-sym; Id→Fun; Id→Fun'; Id→Funs-agree; 𝟙-is-not-𝟘;  ₁-is-not-₀; decidable; has-decidable-equality; 𝟚-has-decidable-equality; not-zero-is-one; inl-inr-disjoint-images; disjunctive-syllogism; s≢0;pred; succ-elim; succ-lc; ℕ-decidable; ℕ-has-decidable-equality)

open import UF-Singleton using (is-center; is-singleton; 𝟙-is-singleton; center; centrality; is-subsingleton; 𝟘-is-subsingleton; singletons-are-subsingletons; 𝟙-is-subsingleton; pointed-subsingletons-are-singletons; singleton-iff-pointed-and-subsingleton; is-prop; is-truth-value; is-set; EM; em; EM'; em'; EM→EM'; EM'→EM; no-unicorns; em-irrefutable; general-em-irrefutable)

open import UF-Monoid using(Magma; ⟨_⟩; magma-is-set; magma-operation;  is-magma-hom; id-is-magma-hom; is-magma-iso; id-is-magma-iso; Id→iso; Id→iso-is-iso; _≅ₘ_; magma-Id→iso; ∞-Magma;   left-neutral; right-neutral; associative; Monoid; invleft; invright; Group)

open import UF-Equality using (refl-left; refl-right; ∙assoc; ⁻¹-left∙; ⁻¹-right∙; ⁻¹-involutive; ap-refl; ap-∙; ap⁻¹; ap-id; ap-∘; transport∙; Nat; Nats-are-natural; NatΣ; transport-ap; apd; to-Σ-≡; from-Σ-≡; to-Σ-≡'; _is-of-hlevel_; wconstant; wconstant-endomap; wcmap; wcmap-constancy; Hedberg; wconstant-≡-endomaps; sets-have-wconstant-≡-endomaps; types-with-wconstant-≡-endomaps-are-sets; subsingletons-have-wconstant-≡-endomaps; subsingletons-are-sets; singletons-are-sets; 𝟘-is-set; 𝟙-is-set; subsingletons-are-of-hlevel-1; types-of-hlevel-1-are-subsingletons; sets-are-of-hlevel-2; types-of-hlevel-2-are-sets; hlevel-upper; _has-minimal-hlevel_; _has-minimal-hlevel-∞; 𝟙-is-of-hlevel-2; pointed-types-have-wconstant-endomap; empty-types-have-wconstant-endomap; decidable-has-wconstant-endomap; hedberg-lemma; hedberg; ℕ-is-set; 𝟚-is-set; has-section; has-right-inv; _◁_; retraction; section; retract-equation; id-◁; ℕ-◁-ℕ-id; ℕ-◁-ℕ-pred; ℕ-◁-ℕ-add-two; _◁∘_; _◁⟨_⟩_; _◀; Σ-retract; transport-is-retraction; transport-is-section; Σ-reindexing-retract; singleton-type; singleton-type-center; singleton-type-centered; singleton-types-are-singletons; retract-of-singleton; singleton-type'; singleton-type'-center; singleton-type'-centered; singleton-types'-are-singletons; invertible; fiber; fiber-point; fiber-identification; is-equiv; inverse; inverses-are-sections; inv-elim-right; inverse-centrality; inverses-are-retractions; inv-elim-left; equivs-are-invertible; invertibles-are-equivs;  inverses-are-equivs; inv-equiv; inversion-involutive; inverse-involution; id-invertible; ∘-invertible; id-is-equiv; ∘-is-equiv; inverse-of-∘; _≃_;  Eq→fun-is-equiv; invertibility-gives-≃; Σ-induction-≃; Σ-flip; ×-comm; id-≃; _●_; ≃-sym; _≃⟨_⟩_; _■; transport-is-equiv; Σ-≡-≃; to-×-≡; from-×-≡; ×-≡-≃; ap-pr₁-to-×-≡; ap-pr₂-to-×-≡; Σ-cong; ≃-gives-◁; equiv-to-singleton)

open import UF-Univalence using (Id→Eq; is-univalent; univalence-≃; Eq→Id; Id→fun; Id→funs-agree; swap₂; swap₂-involutive; swap₂-is-equiv; subsingleton-criterion; subsingleton-criterion'; retract-of-subsingleton; left-cancellable; injective; lc-maps-reflect-subsingletons; has-retraction; has-left-inv; sections-are-lc; equivs-have-retractions; equivs-have-sections; equivs-are-lc; equiv-to-subsingleton; comp-inverses; subtypes-of-sets-are-sets; equiv-to-set; sections-closed-under-∼; retractions-closed-under-∼; is-joyal-equiv; one-inverse; joyal-equivs-are-invertible; joyal-equivs-are-equivs; invertibles-are-joyal-equivs; equivs-are-joyal-equivs; equivs-closed-under-∼; equiv-to-singleton'; pr₁-lc; subsets-of-sets-are-sets; to-subtype-≡; pr₁-equiv; pr₁-≃; ΠΣ-distr-≃; Σ-assoc; ⁻¹-is-equiv; ⁻¹-≃; singleton-types-≃; singletons-≃; maps-of-singletons-are-equivs; logically-equivalent-subsingletons-are-equivalent; singletons-are-equivalent; NatΣ-fiber-equiv; NatΣ-equiv-gives-fiberwise-equiv; Σ-is-subsingleton; ×-is-singleton; ×-is-subsingleton; ×-is-subsingleton'; ×-is-subsingleton'-back; ap₂; equiv-singleton-lemma; singleton-equiv-lemma; univalence⇒; ⇒univalence; univalence→; →univalence; 𝔾-≃; 𝔾-≃-equation; ℍ-≃; ℍ-≃-equation; 𝕁-≃; 𝕁-≃-equation; ℍ-equiv; 𝕁-equiv; 𝕁-invertible; automatic-equiv-functoriality; Σ-change-of-variable'; Σ-change-of-variable''; transport-map-along-≡; transport-map-along-≃; is-hae; haes-are-invertible; transport-ap-≃; equivs-are-haes; half-adjoint-condition; Σ-change-of-variable)

open import UF-Extensionality using(funext; precomp-is-equiv; univalence-gives-funext; dfunext; happly; hfunext; hfunext-gives-dfunext; vvfunext; dfunext-gives-vvfunext; postcomp-invertible; postcomp-is-equiv; vvfunext-gives-hfunext; funext-gives-vvfunext; funext-gives-hfunext; dfunext-gives-hfunext; funext-gives-dfunext; univalence-gives-dfunext'; univalence-gives-hfunext'; univalence-gives-vvfunext'; univalence-gives-hfunext; univalence-gives-dfunext; univalence-gives-vvfunext; Π-is-subsingleton; being-singleton-is-subsingleton; being-equiv-is-subsingleton; subsingletons-are-retracts-of-logically-equivalent-types; equivalence-property-is-retract-of-invertibility-data; univalence-is-subsingleton; Univalence; univalence-is-subsingletonω; univalence-is-singleton; global-dfunext; univalence-gives-global-dfunext; global-hfunext; univalence-gives-global-hfunext; ∃!; -∃!; ∃!-is-subsingleton; unique-existence-gives-weak-unique-existence; weak-unique-existence-gives-unique-existence-sometimes; subsingleton-univalence-≃; Ω; _holds; holds-is-subsingleton; Ω-ext; Ω-is-a-set; powersets-are-sets; 𝓟; powersets-are-sets'; _∈_; _⊆_; ∈-is-subsingleton; ⊆-is-subsingleton; ⊆-refl; ⊆-refl-consequence; subset-extensionality; subset-extensionality')

-- UF-Embedding.agda
open import UF-Embedding using (_↪_; id-≃-left; ≃-sym-left-inverse; ≃-sym-right-inverse; ≃-Sym; ≃-Comp; Eq-Eq-cong'; Eq-Eq-cong; is-embedding; being-embedding-is-subsingleton; pr₂-embedding; pr₁-embedding; equivs-are-embeddings; id-is-embedding; ∘-embedding; embedding-lemma; embedding-criterion; ap-is-equiv-gives-embedding; embedding-gives-ap-is-equiv; embedding-criterion-converse; embeddings-are-lc; 𝓨; 𝑌; transport-lemma; 𝓔; 𝓝; yoneda-η; yoneda-ε; is-fiberwise-equiv; 𝓔-is-equiv; 𝓝-is-equiv; Yoneda-Lemma; retract-universal-lemma; fiberwise-equiv-universal; universal-fiberwise-equiv; hfunext→; →hfunext; fiberwise-equiv-criterion; fiberwise-equiv-criterion'; _≃̇_; is-representable; representable-universal; universal-representable; fiberwise-retractions-are-equivs; fiberwise-◁-gives-≃; embedding-criterion'; being-fiberwise-equiv-is-subsingleton; being-representable-is-subsingleton; 𝓨-is-embedding; Lift; lift; lower; type-of-Lift; type-of-lower; type-of-lift; Lift-induction; Lift-recursion; lower-lift; lift-lower; Lift-≃; ≃-Lift; Subtypes; _/[_]_; χ-special; is-special-map-classifier; mc-gives-sc; χ-special-is-equiv; special-map-classifier; Ω-is-subtype-classifier; subtypes-form-set; 𝓢; equiv-classification; the-singletons-form-a-singleton; univalence-→-again)

open import UF-Truncation using (is-inhabited; inhabitation-is-subsingleton; inhabited-intro; inhabited-recursion; inhabited-recursion-computation; inhabited-induction; inhabited-computation ; inhabited-subsingletons-are-pointed; inhabited-functorial; image'; restriction'; corestriction'; is-surjection'; subsingleton-truncations-exist)

open UF-Truncation.basic-truncation-development using (∥_∥; ∥∥-is-subsingleton; ∣_∣; ∥∥-recursion; hunapply; ∥∥-recursion-computation; ∥∥-induction; ∥∥-computation; ∥∥-functor; ∥∥-agrees-with-inhabitation; _∨_; ∃; -∃; ∨-is-subsingleton; ∃-is-subsingleton; image; restriction; corestriction; is-surjection; being-surjection-is-subsingleton; corestriction-surjection; surjection-induction; ∣∣-is-surjection; singletons-are-inhabited; inhabited-subsingletons-are-singletons; singleton-iff-inhabited-subsingleton; equiv-iff-embedding-and-surjection; equiv-≡-embedding-and-surjection; fix; from-fix; to-fix; fix-is-subsingleton; choice-function; wconstant-endomap-gives-choice-function; choice-function-gives-wconstant-endomap; wconstant-endomap-gives-∥∥-choice-function; ∥∥-choice-function-gives-wconstant-endomap; ∥∥-recursion-set)

open import UF-Structures

--open UF-Structures.sip using(⟨_⟩; structure; ⟦_⟧; canonical-map; SNS; homomorphic; _≃[_]_; Id→homEq; homomorphism-lemma; characterization-of-≡; Id-homEq-is-equiv; canonical-map-charac; when-canonical-map-is-equiv; canonical-map-equiv-criterion; canonical-map-equiv-criterion')

open UF-Structures.∞-magma-identity using (∞-magma-structure; ∞-Magma; sns-data; _≅_; characterization-of-∞-Magma-≡; characterization-of-characterization-of-∞-Magma-≡)

--open UF-Structures.sip-with-axioms using ([_]; ⟪_⟫; add-axioms; characterization-of-≡-with-axioms)
open UF-Structures.magma-identity using (Magma; _≅_; characterization-of-Magma-≡; characterization-of-characterization-of-Magma-≡)

open UF-Structures.pointed-type-identity using(Pointed; sns-data; _≅_; characterization-of-pointed-type-≡; characterization-of-characterization-of-pointed-type-≡)

--open UF-Structures.sip-join using (technical-lemma; ⟪_⟫; [_]₀; [_]₁; join; _≃⟦_,_⟧_; characterization-of-join-≡)

--open Structures.pointed-∞-magma-identity using (_≅_; characterization-of-pointed-magma-≡; characterization-of-characterization-of-pointed-magma-≡)

open UF-Structures.monoid-identity using (dfe; monoid-structure; monoid-axioms; Monoid; sns-data; _≅_; characterization-of-monoid-≡; characterization-of-characterization-of-monoid-≡)

open UF-Structures.associative-∞-magma-identity using (fe; associative; ∞-amagma-structure; ∞-aMagma; homomorphic; respect-assoc; remark; sns-data; _≅_; characterization-of-∞-aMagma-≡)

--open UF-Structures.group-identity using (hfe; group-structure; group-axiom; Group; inv-lemma; group-axiom-is-subsingleton; sns-data; _≅_; characterization-of-group-≡; characterization-of-characterization-of-group-≡; _≅'_; group-structure-of; monoid-structure-of; monoid-axioms-of; multiplication; unit; group-is-set; unit-left; unit-right; assoc; inv; inv-left; inv-is-left-inv; inv-right; inv-is-right-inv; preserves-multiplication; preserves-unit; idempotent-is-unit; unit-preservation-lemma; inv-unique; left-inv-unique; right-inv-unique; preserves-inv; inv-preservation-lemma; is-homomorphism; preservation-of-mult-is-subsingleton; being-hom-is-subsingleton; notions-of-homomorphism-agree; ≅-agreement; forget-unit-preservation; NB; forget-unit-preservation-is-equiv)

-- open UF-Structures.subgroup-identity using (gfe; _·_; group-closed; Subgroups; ⟪_⟫; being-group-closed-subset-is-subsingleton; ⟪⟫-is-embedding; ap-⟪⟫; ap-⟪⟫-is-equiv; subgroups-form-a-set; subgroup-equality-gives-membership-equiv; membership-equiv-gives-carrier-equality; membership-equiv-gives-subgroup-equality; subgroup-equality; T;  h-lc; having-group-closed-fiber-is-subsingleton; at-most-one-homomorphic-structure; group-closed-fiber-gives-homomorphic-structure; homomorphic-structure-gives-group-closed-fiber; fiber-structure-lemma; characterization-of-the-type-of-subgroups; induced-group)

open UF-Structures.slice-identity using (S; sns-data)
