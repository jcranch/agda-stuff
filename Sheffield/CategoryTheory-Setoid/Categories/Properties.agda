module Sheffield.CategoryTheory-Setoid.Categories.Properties where

open import Function renaming (id to i)
open import Function.Equality
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality


introduce-opop : {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) → Functor C (opposite (opposite C))
introduce-opop C = record {
  obj = i ;
  hom = id ;
  id = λ x → ≈-refl ;
  compose = λ g f → ≈-refl } where
  open Category C hiding (id)

eliminate-opop : {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) → Functor (opposite (opposite C)) C
eliminate-opop C = record {
  obj = i ;
  hom = id ;
  id = λ x → ≈-refl ;
  compose = λ g f → ≈-refl } where
  open Category C hiding (id)


opop-equivalence : {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) → opposite (opposite C) ≅₀ C
opop-equivalence C = equivalent₀ (eliminate-opop C) (introduce-opop C) I J where
  open Category C renaming (id to i1)
  I : introduce-opop C ⊙ eliminate-opop C ≅₁ idFunctor (opposite (opposite C))
  I = isomorphic₁ Ψ Φ (make-≈₂ (λ x → id-l _)) (make-≈₂ (λ x → id-l _)) where
    Ψ = record {
      component = i1 ;
      naturality = λ f → ≈-trans (id-l f) (≈-sym (id-r f)) }
    Φ = record {
      component = i1 ;
      naturality = λ f → ≈-trans (id-l f) (≈-sym (id-r f)) }
  J : eliminate-opop C ⊙ introduce-opop C ≅₁ idFunctor C
  J = isomorphic₁ Ψ Φ (make-≈₂ (λ x → id-l _)) (make-≈₂ (λ x → id-l _)) where
    Ψ = record {
      component = i1 ;
      naturality = λ f → ≈-trans (id-l f) (≈-sym (id-r f)) }
    Φ = record {
      component = i1 ;
      naturality = λ f → ≈-trans (id-l f) (≈-sym (id-r f)) }
