module Sheffield.CategoryTheory-Setoid.Functors.CompositionEqualities where

open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Composition
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality


module ⊙-units {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) where

  ⊙-unital-l : idFunctor D ⊙ F ≅₁ F
  ⊙-unital-l = isomorphic₁ (⊙-unitor-l F) (⊙-unitor-l⁻¹ F) (make-≈₂ (λ x → Category.id-r D _)) (make-≈₂ (λ x → Category.id-r D _))

  ⊙-unital-r : F ⊙ idFunctor C ≅₁ F
  ⊙-unital-r = isomorphic₁ (⊙-unitor-r F) (⊙-unitor-r⁻¹ F) (make-≈₂ (λ x → Category.id-r D _)) (make-≈₂ (λ x → Category.id-r D _))

open ⊙-units public

module ⊙-associativity {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ ℓ₄ ℓ′₄ ℓ″₄ : Level} {B : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {D : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} {E : Category {ℓ₄} {ℓ′₄} {ℓ″₄}} (H : Functor D E) (G : Functor C D) (F : Functor B C) where

  ⊙-associative : (H ⊙ G) ⊙ F ≅₁ H ⊙ (G ⊙ F)
  ⊙-associative = isomorphic₁ (⊙-associator H G F) (⊙-associator⁻¹ H G F) (make-≈₂ (λ x → Category.id-r E _)) (make-≈₂ (λ x → Category.id-r E _))

open ⊙-associativity public